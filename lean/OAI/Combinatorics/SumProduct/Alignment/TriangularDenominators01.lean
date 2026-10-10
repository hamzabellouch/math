import Mathlib
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
noncomputable section
end

end
 

section
 

 

section
 

 

section
 

 

 
section

 

namespace CocompactLattice
open scoped Pointwise
open Set Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

lemma closure_eq_top_of_nhds [PreconnectedSpace G] {U : Set G} (hU : U ∈ nhds (1:G)) :
    Subgroup.closure U = ⊤ := by
  have hopen := (Subgroup.closure U).isOpen_of_mem_nhds
    (Filter.mem_of_superset hU (Subgroup.subset_closure (k := U)))
  have hclosed := (Subgroup.closure U).isClosed_of_isOpen hopen
  have huniv := (show IsClopen (Subgroup.closure U : Set G) from ⟨hclosed,hopen⟩).eq_univ
    ⟨1,(Subgroup.closure U).one_mem⟩
  exact SetLike.coe_injective huniv

 

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma generating_intersection (Γ : Subgroup G) (C U : Set G)
    (h1C : (1:G) ∈ C) (h1U : (1:G) ∈ U)
    (hsym : ∀ u ∈ U, u⁻¹ ∈ U) (hgen : Subgroup.closure U = ⊤)
    (hreps : ∀ g : G, ∃ c ∈ C, c⁻¹*g ∈ Γ) :
    Subgroup.closure (↑Γ ∩ (C⁻¹ * U * C)) = Γ := by
  let S : Set G := ↑Γ ∩ (C⁻¹ * U * C)
  let H := Subgroup.closure S
  have hHΓ : H ≤ Γ := by
    change Subgroup.closure S ≤ Γ
    rw [Subgroup.closure_le]
    exact fun _ h => h.1
  have hstep (u : G) (hu : u ∈ U) (c : G) (hc : c ∈ C) :
      u*c ∈ C*(H:Set G) := by
    obtain ⟨v,hv,hvΓ⟩ := hreps (u*c)
    have hδ : v⁻¹*(u*c) ∈ H := by
      apply Subgroup.subset_closure
      refine ⟨hvΓ,?_⟩
      rw [← mul_assoc]
      exact Set.mul_mem_mul (Set.mul_mem_mul (by simpa using hv) hu) hc
    exact ⟨v,hv,v⁻¹*(u*c),hδ,by group⟩
  have hleft (u : G) (hu : u ∈ U) {g : G} (hg : g ∈ C*(H:Set G)) :
      u*g ∈ C*(H:Set G) := by
    obtain ⟨c,hc,h,hh,rfl⟩ := hg
    obtain ⟨v,hv,δ,hδ,heq⟩ := hstep u hu c hc
    change v*δ = u*c at heq
    refine ⟨v,hv,δ*h,H.mul_mem hδ hh,?_⟩
    change v * (δ*h) = u * (c*h)
    calc
      v * (δ*h) = (v*δ)*h := (mul_assoc _ _ _).symm
      _ = u*(c*h) := by rw [heq,mul_assoc]
  have hall (g : G) : g ∈ C*(H:Set G) := by
    have hg : g ∈ Subgroup.closure U := hgen.symm ▸ Subgroup.mem_top g
    apply Subgroup.closure_induction_left
      (p := fun g _ => g ∈ C*(H:Set G)) ?_ ?_ ?_ hg
    · exact ⟨1,h1C,1,H.one_mem,by simp⟩
    · intro u hu g _ hg
      exact hleft u hu hg
    · intro u hu g _ hg
      exact hleft u⁻¹ (hsym u hu) hg
  apply le_antisymm hHΓ
  intro g hg
  obtain ⟨c,hc,h,hh,heq⟩ := hall g
  have hcΓ : c ∈ Γ := by
    have hx := Γ.mul_mem hg (Γ.inv_mem (hHΓ hh))
    rw [← heq,mul_inv_cancel_right] at hx
    exact hx
  have hcH : c ∈ H := by
    apply Subgroup.subset_closure
    refine ⟨hcΓ,?_⟩
    convert Set.mul_mem_mul (Set.mul_mem_mul (show (1:G) ∈ C⁻¹ by simpa using h1C)
      h1U) hc using 1; simp
  rw [← heq]
  exact H.mul_mem hcH hh

 
theorem fg_of_compact_reps [PreconnectedSpace G] [LocallyCompactSpace G] [T2Space G]
    (Γ : Subgroup G) [DiscreteTopology Γ] (C : Set G) (hC : IsCompact C)
    (hreps : ∀ g : G, ∃ c ∈ C, c⁻¹*g ∈ Γ) : Γ.FG := by
  classical
  obtain ⟨V,hV,hVnh⟩ := exists_compact_mem_nhds (1:G)
  let U := V ∩ V⁻¹
  have hU : IsCompact U := hV.inter hV.inv
  have hUnh : U ∈ nhds (1:G) := by
    apply Filter.inter_mem hVnh
    have hv' : V ∈ nhds ((1:G)⁻¹) := by simpa using hVnh
    exact continuous_inv.continuousAt.preimage_mem_nhds hv'
  have h1U : (1:G) ∈ U := mem_of_mem_nhds hUnh
  have hsym : ∀ u ∈ U, u⁻¹ ∈ U := by
    intro u hu
    exact ⟨hu.2,by simpa using hu.1⟩
  let K : Set G := insert 1 C
  have hK : IsCompact K := hC.insert 1
  have hKrep : ∀ g : G, ∃ c ∈ K, c⁻¹*g ∈ Γ := by
    intro g
    obtain ⟨c,hc,hcg⟩ := hreps g
    exact ⟨c,Set.mem_insert_of_mem 1 hc,hcg⟩
  have hbound : IsCompact (K⁻¹ * U * K) := (hK.inv.mul hU).mul hK
  have hfinite : (↑Γ ∩ (K⁻¹*U*K)).Finite := by
    have hc := hbound.inter_right (Subgroup.isClosed_of_discreteTopology (U := Γ))
    have hf := hc.finite (IsDiscrete.mono (show IsDiscrete (Γ:Set G) from ⟨inferInstance⟩)
      Set.inter_subset_right)
    simpa only [Set.inter_comm] using hf
  apply (Subgroup.fg_iff Γ).mpr
  exact ⟨_,generating_intersection Γ K U (Set.mem_insert 1 C) h1U hsym
    (closure_eq_top_of_nhds hUnh) hKrep,hfinite⟩

end CocompactLattice

 

namespace TriangularDenominators
open scoped BigOperators
noncomputable section

def HasDenom (D : ℕ) (x : ℚ) : Prop := ∃ z : ℤ, (D : ℚ) * x = z

lemma denom_zero (D : ℕ) : HasDenom D 0 := ⟨0,by simp⟩
lemma denom_add {D : ℕ} {x y : ℚ} (hx : HasDenom D x) (hy : HasDenom D y) :
    HasDenom D (x+y) := by
  obtain ⟨a,ha⟩ := hx
  obtain ⟨b,hb⟩ := hy
  exact ⟨a+b,by rw [mul_add,ha,hb,Int.cast_add]⟩
lemma denom_neg {D : ℕ} {x : ℚ} (hx : HasDenom D x) : HasDenom D (-x) := by
  obtain ⟨a,ha⟩ := hx
  exact ⟨-a,by rw [mul_neg,ha,Int.cast_neg]⟩
lemma denom_mul {D E : ℕ} {x y : ℚ} (hx : HasDenom D x) (hy : HasDenom E y) :
    HasDenom (D*E) (x*y) := by
  obtain ⟨a,ha⟩ := hx
  obtain ⟨b,hb⟩ := hy
  refine ⟨a*b,?_⟩
  rw [Nat.cast_mul,mul_mul_mul_comm,ha,hb,Int.cast_mul]
lemma denom_mono {D E : ℕ} (h : D ∣ E) {x : ℚ} (hx : HasDenom D x) :
    HasDenom E x := by
  obtain ⟨k,rfl⟩ := h
  obtain ⟨a,ha⟩ := hx
  refine ⟨(k : ℤ)*a,?_⟩
  rw [Nat.cast_mul,mul_comm (D : ℚ),mul_assoc,ha,Int.cast_mul,Int.cast_natCast]
lemma denom_self (x : ℚ) : HasDenom x.den x := by
  refine ⟨x.num,?_⟩
  calc
    (x.den : ℚ) * x = (x.den : ℚ) * ((x.num : ℚ) / x.den) :=
      congrArg ((x.den : ℚ) * ·) (Rat.num_div_den x).symm
    _ = x.num := mul_div_cancel₀ _ (by exact_mod_cast x.den_ne_zero)

lemma finite_common_denom {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ i ∈ s, HasDenom D (f i) := by
  classical
  refine ⟨∏ i ∈ s, (f i).den, Finset.prod_pos (fun i _ => (f i).den_pos),?_⟩
  intro i hi
  apply denom_mono (Finset.dvd_prod_of_mem (fun i => (f i).den) hi)
  exact denom_self _

 

theorem polynomial_grid {ι : Type*} (P : MvPolynomial ι ℚ) (D : ℕ) (hD : 0 < D) :
    ∃ E : ℕ, 0 < E ∧ ∀ x : ι → ℚ, (∀ i, HasDenom D (x i)) →
      HasDenom E (MvPolynomial.eval x P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    exact ⟨a.den,a.den_pos,fun _ _ => by simpa using denom_self a⟩
  | add p q hp hq =>
    obtain ⟨E,hE,hp⟩ := hp
    obtain ⟨F,hF,hq⟩ := hq
    refine ⟨E*F,Nat.mul_pos hE hF,?_⟩
    intro x hx
    rw [map_add]
    exact denom_add (denom_mono (dvd_mul_right E F) (hp x hx))
      (denom_mono (dvd_mul_left F E) (hq x hx))
  | mul_X p i hp =>
    obtain ⟨E,hE,hp⟩ := hp
    refine ⟨E*D,Nat.mul_pos hE hD,?_⟩
    intro x hx
    simpa using denom_mul (hp x hx) (hx i)

variable {G : Type*} [Group G] {n : ℕ}

 

structure Coordinates (G : Type*) [Group G] (n : ℕ) where
  coord : G → Fin n → ℚ
  one_coord : ∀ i, coord 1 i = 0
  correction : (i : Fin n) → MvPolynomial (Fin i.val ⊕ Fin i.val) ℚ
  mul_coord : ∀ g h i, coord (g*h) i = coord g i + coord h i +
    MvPolynomial.eval (Sum.elim (fun j => coord g ⟨j.val,lt_trans j.isLt i.isLt⟩)
      (fun j => coord h ⟨j.val,lt_trans j.isLt i.isLt⟩)) (correction i)

 

theorem closure_grid (c : Coordinates G n) (S : Finset G) :
    ∃ D : ℕ, 0 < D ∧ ∀ g ∈ Subgroup.closure (S : Set G),
      ∀ i, HasDenom D (c.coord g i) := by
  classical
  have hpartial (j : ℕ) (hj : j ≤ n) :
      ∃ D : ℕ, 0 < D ∧ ∀ g ∈ Subgroup.closure (S : Set G),
        ∀ i : Fin n, i.val < j → HasDenom D (c.coord g i) := by
    induction j with
    | zero => exact ⟨1,by decide,fun _ _ i hi => False.elim (Nat.not_lt_zero _ hi)⟩
    | succ j ih =>
      obtain ⟨D,hD,hd⟩ := ih (by omega)
      let i : Fin n := ⟨j,by omega⟩
      obtain ⟨E,hE,he⟩ := polynomial_grid (c.correction i) D hD
      obtain ⟨F,hF,hf⟩ := finite_common_denom S (fun g => c.coord g i)
      let T := D*E*F
      have hDT : D ∣ T := dvd_mul_of_dvd_left (dvd_mul_right D E) F
      have hET : E ∣ T := dvd_mul_of_dvd_left (dvd_mul_left E D) F
      have hFT : F ∣ T := dvd_mul_left F (D*E)
      have herr (g h : G) (hg : g ∈ Subgroup.closure (S : Set G))
          (hh : h ∈ Subgroup.closure (S : Set G)) :
          HasDenom T (MvPolynomial.eval
            (Sum.elim (fun k => c.coord g ⟨k.val,lt_trans k.isLt i.isLt⟩)
              (fun k => c.coord h ⟨k.val,lt_trans k.isLt i.isLt⟩)) (c.correction i)) := by
        apply denom_mono hET
        apply he
        intro k
        rcases k with k | k
        · exact hd g hg _ k.isLt
        · exact hd h hh _ k.isLt
      have hi (g : G) (hg : g ∈ Subgroup.closure (S : Set G)) :
          HasDenom T (c.coord g i) := by
        induction hg using Subgroup.closure_induction with
        | mem g hg => exact denom_mono hFT (hf g hg)
        | one => rw [c.one_coord]; exact denom_zero T
        | mul g h hg hh ig ih =>
          rw [c.mul_coord]
          exact denom_add (denom_add ig ih) (herr g h hg hh)
        | inv g hg ig =>
          have hmul := c.mul_coord g g⁻¹ i
          rw [mul_inv_cancel,c.one_coord] at hmul
          have hx := denom_neg (denom_add ig
            (herr g g⁻¹ hg ((Subgroup.closure (S : Set G)).inv_mem hg)))
          convert hx using 1
          linarith
      refine ⟨T,Nat.mul_pos (Nat.mul_pos hD hE) hF,?_⟩
      intro g hg k hk
      by_cases heq : k.val = j
      · have hk' : k = i := Fin.ext heq
        subst k
        exact hi g hg
      · exact denom_mono hDT (hd g hg k (by omega))
  obtain ⟨D,hD,hd⟩ := hpartial n le_rfl
  exact ⟨D,hD,fun g hg i => hd g hg i i.isLt⟩

lemma denom_small {D : ℕ} (hD : 0 < D) {x : ℚ} (hx : HasDenom D x)
    (hsmall : |x| < 1 / (D : ℚ)) : x = 0 := by
  obtain ⟨z,hz⟩ := hx
  have hp : (0 : ℚ) < D := by exact_mod_cast hD
  have hzsmall : |(z : ℚ)| < 1 := by
    rw [← hz,abs_mul,abs_of_pos hp]
    calc
      (D : ℚ) * |x| < (D : ℚ) * (1 / (D : ℚ)) := mul_lt_mul_of_pos_left hsmall hp
      _ = 1 := mul_div_cancel₀ _ hp.ne'
  have hzi : |z| < 1 := by exact_mod_cast hzsmall
  have heq := Int.abs_lt_one_iff.mp hzi
  rw [heq,Int.cast_zero] at hz
  exact (mul_eq_zero.mp hz).resolve_left hp.ne'

 

theorem closure_discrete [TopologicalSpace G] [IsTopologicalGroup G]
    (c : Coordinates G n) (hinj : Function.Injective c.coord)
    (hcont : ∀ i, Continuous (fun g => c.coord g i)) (S : Finset G) :
    DiscreteTopology (Subgroup.closure (S : Set G)) := by
  obtain ⟨D,hD,hd⟩ := closure_grid c S
  let H := Subgroup.closure (S : Set G)
  have hopen : IsOpen (⋂ i : Fin n, {g : H | |c.coord g i| < 1 / (D : ℚ)}) := by
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt ((hcont i).comp continuous_subtype_val).abs continuous_const
  have heq : (⋂ i : Fin n, {g : H | |c.coord g i| < 1 / (D : ℚ)}) = {1} := by
    ext g
    simp only [Set.mem_iInter,Set.mem_ofPred_eq,Set.mem_singleton_iff]
    constructor
    · intro hg
      apply Subtype.ext
      apply hinj
      funext i
      change c.coord (g : G) i = c.coord 1 i
      rw [c.one_coord]
      exact denom_small hD (hd g g.property i) (hg i)
    · rintro rfl
      intro i
      simp only [OneMemClass.coe_one,c.one_coord,abs_zero]
      exact one_div_pos.mpr (by exact_mod_cast hD)
  rw [heq] at hopen
  exact discreteTopology_of_isOpen_singleton_one hopen

variable [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

 

theorem finiteIndex_of_compact_reps (Γ Λ : Subgroup G) (hΓ : Γ ≤ Λ)
    [DiscreteTopology Λ] (C : Set G) (hC : IsCompact C)
    (hrep : ∀ g : G, ∃ c ∈ C, c⁻¹*g ∈ Γ) :
    (Γ.subgroupOf Λ).FiniteIndex := by
  let K : Set Λ := (Subtype.val : Λ → G) ⁻¹' C
  have hK : K.Finite :=
    ((Subgroup.isClosed_of_discreteTopology (U := Λ)).isClosedEmbedding_subtypeVal.isCompact_preimage
      hC).finite_of_discrete
  let : Finite K := hK.to_subtype
  apply Subgroup.finiteIndex_iff_finite_quotient.mpr
  apply Finite.of_surjective (fun c : K => (QuotientGroup.mk c.val : Λ ⧸ Γ.subgroupOf Λ))
  intro q
  obtain ⟨g,rfl⟩ := Quotient.exists_rep q
  obtain ⟨c,hc,hcg⟩ := hrep g
  have hcΛ : c ∈ Λ := by
    have h := Λ.mul_mem g.property (Λ.inv_mem (hΓ hcg))
    simpa only [mul_inv_rev,inv_inv,mul_inv_cancel_left] using h
  refine ⟨⟨⟨c,hcΛ⟩,hc⟩,?_⟩
  apply QuotientGroup.eq.mpr
  exact hcg

end
end TriangularDenominators

 

end
end
end
end

end OAI
