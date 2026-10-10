import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceCellSumsDensity

namespace OAI

noncomputable section
namespace Ostmann.Characters
open scoped BigOperators

theorem exists_uniform_cell_residue_cover (c : ℝ) (hc : 0<c) :
    ∃ R : ℕ, ∀ {I : Finset ℕ} (C : NormalizedCellSet I) {b : ℝ},
      0<b → 2 ≤ c*b → c*b ≤ (I.card:ℝ) →
      b ≤ (C.base:ℝ) → ((C.base+C.gcd*C.endpoint:ℕ):ℝ) ≤ 3*b →
      ∃ r ≤ R, ∀ z : ZMod C.endpoint, ∃ f : Fin r → ℕ,
        (∀ i, f i∈C.cells) ∧ ∑ i,(f i:ZMod C.endpoint)=z := by
  obtain ⟨δ,hδ0,hδc⟩ := exists_rat_btwn (by positivity : (0:ℝ)<c/12)
  have hδ : (0:ℚ)<δ := by exact_mod_cast hδ0
  obtain ⟨R,hR⟩ := exists_uniform_sum_cover_length δ hδ
  refine ⟨R,?_⟩
  intro I C b hb hlarge hcard hbase hmax
  classical
  let : NeZero C.endpoint := ⟨C.endpoint_pos.ne'⟩
  let A := C.cells.image (fun x:ℕ => (x:ZMod C.endpoint))
  have h0 : (0:ZMod C.endpoint)∈A := Finset.mem_image.mpr ⟨0,C.zero_mem,by simp⟩
  have hm := C.real_margins hb hc hlarge hcard hbase hmax
  have hsize : (δ:ℝ)*(C.endpoint:ℝ) ≤ (A.card:ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hδc.le (Nat.cast_nonneg C.endpoint)
    have h2 := mul_le_mul_of_nonneg_left hm.2.2.1 (by positivity : 0 ≤ c/12)
    have hres := hm.2.2.2
    change (c/2)*b ≤ (A.card:ℝ) at hres
    nlinarith
  have hsize' : δ*(Fintype.card (ZMod C.endpoint):ℚ) ≤ A.card := by
    rw [ZMod.card]
    exact_mod_cast hsize
  obtain ⟨r,hr,hcover⟩ := hR (ZMod C.endpoint) A h0 C.residue_generates hsize'
  refine ⟨r,hr,?_⟩
  intro z
  obtain ⟨f,hf,hfsum⟩ := hcover z
  have hpre : ∀ i:Fin r, ∃ x:ℕ,x∈C.cells ∧ (x:ZMod C.endpoint)=f i :=
    fun i=>Finset.mem_image.mp (hf i)
  choose g hg hgf using hpre
  exact ⟨g,hg,by simpa only [hgf] using hfsum⟩

theorem NormalizedCellSet.lift_list {I : Finset ℕ} (C : NormalizedCellSet I)
    {r n t : ℕ} (hr : r≤n) (htlo : r*C.endpoint≤t) (hthi : t≤(n-r)*C.endpoint)
    (hcover : ∀ z:ZMod C.endpoint,∃ f:Fin r→ℕ,
      (∀ i,f i∈C.cells) ∧ ∑i,(f i:ZMod C.endpoint)=z) :
    ∃ l : List ℕ, l.length=n ∧ (∀ x∈l,x∈I) ∧ l.sum=n*C.base+C.gcd*t := by
  obtain ⟨l,hlen,hmem,hsum⟩ := lift_residue_cover_to_interval C.cells C.endpoint_pos
    C.zero_mem C.endpoint_mem C.cells_le hr htlo hthi hcover
  refine ⟨l.map (fun x=>C.base+C.gcd*x),by simpa using hlen,?_,?_⟩
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    have hh : C.base+C.gcd*y∈C.cells.image (fun x=>C.base+C.gcd*x) :=
      Finset.mem_image.mpr ⟨y,hmem y hy,rfl⟩
    simpa only [C.recover] using hh
  · have hid : ∀ l : List ℕ,
        (l.map (fun x=>C.base+C.gcd*x)).sum=l.length*C.base+C.gcd*l.sum := by
      intro l
      induction l with
      | nil => simp
      | cons a l ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih]; ring
    rw [hid,hlen,hsum]

end Ostmann.Characters

end

end OAI
