import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.GridSpreadTrace
import OAI.Probability.LatticeSurface.Coercivity.GridTrace
import OAI.Probability.LatticeSurface.Coercivity.GridTraceAnalytic
import OAI.Probability.LatticeSurface.Coercivity.GridTraceGeometry
import OAI.Probability.LatticeSurface.Coercivity.GridTraceKernel
import OAI.Probability.LatticeSurface.Coercivity.GridTraceMain
import OAI.Probability.LatticeSurface.Coercivity.GridTraceScale
import OAI.Probability.LatticeSurface.Coercivity.GridTraceTelescope

namespace OAI

noncomputable section

open scoped BigOperators

namespace GridTrace

lemma walk_integer_intermediate {V : Type*} (G : SimpleGraph V) (c : V → ℤ)
    (hedge : ∀ ⦃x y⦄, G.Adj x y → c y ≤ c x+1) {x y : V}
    (w : G.Walk x y) (k : ℤ) (hx : c x ≤ k) (hy : k ≤ c y) :
    ∃ z∈w.support,c z=k := by
  classical
  induction w with
  | @nil a => exact ⟨a,by simp,by omega⟩
  | @cons a b d hab w ih =>
    by_cases ha : c a=k
    · exact ⟨a,by simp,ha⟩
    by_cases hb : k ≤ c b
    · have hh := hedge hab
      exact ⟨b,by simp,by omega⟩
    obtain ⟨z,hz,hzk⟩ := ih (by omega) hy
    exact ⟨z,by simp [hz],hzk⟩

lemma connected_projection (P : Finset Vertex) (G : SimpleGraph P) (hG : G.Preconnected)
    (c : Vertex → ℤ) (hedge : ∀ ⦃x y : P⦄,G.Adj x y → c y ≤ c x+1)
    (a b : P) (k : ℤ) (hak : c a ≤ k) (hkb : k ≤ c b) :
    ∃ z∈P,c z=k := by
  obtain ⟨w⟩ := hG a b
  obtain ⟨z,hz,hzk⟩ := walk_integer_intermediate G (fun z => c z) hedge w k hak hkb
  exact ⟨z,z.property,hzk⟩

lemma strip_size (S : Finset Vertex) (c : Vertex → ℤ) (hc : Set.InjOn c S)
    (z : Vertex) (r : ℝ) (hr : 0 ≤ r)
    (hS : ∀ x∈S, |(c x:ℝ)-c z| ≤ r) :
    (S.card:ℝ) ≤ 2*r+1 := by
  classical
  let n := ⌊r⌋₊
  have hn : (n:ℝ) ≤ r := Nat.floor_le hr
  have hsub : S.image c ⊆ Finset.Icc (c z-(n:ℤ)) (c z+n) := by
    intro k hk
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hk
    have hb : (c x-c z).natAbs ≤ n := by
      apply (Nat.le_floor_iff hr).mpr
      have he : ((c x-c z).natAbs:ℝ)=|(c x:ℝ)-c z| := by
        rw [← Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs,Int.cast_sub]
      rw [he];exact hS x hx
    have hb' : -(n:ℤ) ≤ c x-c z ∧ c x-c z ≤ n := by
      have hh : ((c x-c z).natAbs:ℤ) ≤ (n:ℤ) := by exact_mod_cast hb
      simpa only [Int.natCast_natAbs,abs_le] using hh
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have hcS : (S.image c).card=S.card := Finset.card_image_of_injOn hc
  have hcard := Finset.card_le_card hsub
  rw [hcS,Int.card_Icc] at hcard
  have hce : (c z+n+1-(c z-n)).toNat=2*n+1 := by omega
  rw [hce] at hcard
  have hcard' : (S.card:ℝ) ≤ 2*(n:ℝ)+1 := by exact_mod_cast hcard
  linarith

lemma projection_pin_measure (N : ℕ) (P : Finset Vertex) (hPQ : P ⊆ square N)
    (c : Vertex → ℤ) (hc : ∀ x y, |(c x:ℝ)-c y| ≤ dist₁ x y)
    (a b : ℤ) (hab : a ≤ b) (hproj : ∀ k∈Finset.Icc a b, ∃ z∈P,c z=k) :
    ∃ ν : Vertex → ℝ,
      (∀ x,0 ≤ ν x) ∧ (∀ x, x∉P → ν x=0) ∧
      (∑ x∈square N,ν x)=1 ∧
      ∀ z r, 0 ≤ r → (∑ x∈ball N z r,ν x) ≤ (2*r+1)/(b-a+1:ℤ) := by
  classical
  let I := Finset.Icc a b
  let f : I → Vertex := fun k => Classical.choose (hproj k k.property)
  have hfP (k : I) : f k∈P := (Classical.choose_spec (hproj k k.property)).1
  have hfc (k : I) : c (f k)=k := (Classical.choose_spec (hproj k k.property)).2
  have hfinj : Function.Injective f := by
    intro k l h
    apply Subtype.ext
    rw [← hfc k,← hfc l,h]
  let S : Finset Vertex := Finset.univ.image f
  have hSP : S⊆P := by
    intro z hz
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hz
    exact hfP k
  have hSinj : Set.InjOn c S := by
    intro x hx y hy hh
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hy
    have hkl : k=l := Subtype.ext (by simpa only [hfc] using hh)
    rw [hkl]
  have hcard : (S.card:ℝ) = (b-a+1:ℤ) := by
    dsimp only [S]
    rw [Finset.card_image_of_injective _ hfinj,Finset.card_univ,Fintype.card_coe,Int.card_Icc]
    have hh : ((b+1-a).toNat:ℤ)=b-a+1 := by omega
    exact_mod_cast hh
  have hpos : (0:ℝ)<(b-a+1:ℤ) := by exact_mod_cast (show (0:ℤ)<b-a+1 by omega)
  let ν : Vertex → ℝ := fun x => if x∈S then ((b-a+1:ℤ):ℝ)⁻¹ else 0
  refine ⟨ν,?_,?_,?_,?_⟩
  · intro x;dsimp [ν];split_ifs <;> positivity
  · intro x hx;exact ite_eq_right (fun hs => hx (hSP hs))
  · change (∑ x∈square N,if x∈S then ((b-a+1:ℤ):ℝ)⁻¹ else 0)=1
    rw [← Finset.sum_filter]
    have hfilter : (square N).filter (fun x => x∈S)=S := by
      ext x
      simp only [Finset.mem_filter]
      exact ⟨And.right,fun hx => ⟨hPQ (hSP hx),hx⟩⟩
    rw [hfilter,Finset.sum_const,nsmul_eq_mul,hcard,mul_inv_cancel₀ hpos.ne']
  · intro z r hr
    change (∑ x∈ball N z r,if x∈S then ((b-a+1:ℤ):ℝ)⁻¹ else 0) ≤ _
    rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hpos.le)
    apply strip_size _ c (hSinj.mono (by intro x hx;exact (Finset.mem_filter.mp hx).2)) z r hr
    intro x hx
    have hx := (Finset.mem_filter.mp hx).1
    have hd := (Finset.mem_filter.mp hx).2
    have hc' := hc z x
    rw [abs_sub_comm] at hc'
    exact hc'.trans hd

end GridTrace

end

end OAI
