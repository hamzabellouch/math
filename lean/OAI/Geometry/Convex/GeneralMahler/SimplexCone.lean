import OAI.Geometry.Convex.GeneralMahler.Orthant
import OAI.Geometry.Convex.GeneralMahler.Lift

namespace OAI

/-! §§01,06: Full-dimensional simplicial cones and simplex sections. -/
noncomputable section
open Set Module
open scoped RealInnerProductSpace ENNReal Topology
namespace GeneralMahler
variable {n : ℕ}

/-- Exact affine simplex family. -/
def IsSimplex (K : Set (Rn n)) : Prop :=
  ∃ v : Fin (n+1) → Rn n, AffineIndependent ℝ v ∧ K = convexHull ℝ (range v)

theorem lift_finrank (n : ℕ) : finrank ℝ (LiftSpace n) = n+1 := by
  rw [(WithLp.linearEquiv 2 ℝ (ℝ × Rn n)).finrank_eq]
  simp [Rn, add_comm]

-- two projection maps for finite linear combinations
def hgtL : LiftSpace n →ₗ[ℝ] ℝ where
  toFun := hgt
  map_add' := hgt_add
  map_smul' := hgt_smul
def horizL : LiftSpace n →ₗ[ℝ] Rn n where
  toFun := horiz
  map_add' := horiz_add
  map_smul' := horiz_smul
@[simp] theorem hgtL_apply (x) : @hgtL n x = hgt x := rfl
@[simp] theorem horizL_apply (x) : @horizL n x = horiz x := rfl

lemma independence_lift {ι : Type*} (v : ι → Rn n) :
    AffineIndependent ℝ v ↔ LinearIndependent ℝ (fun i => pair 1 (v i)) := by
  rw [linearIndependent_iff']
  constructor
  · intro h s w hw
    have h₁ := congrArg hgtL hw
    have h₂ := congrArg horizL hw
    simp only [map_sum,map_smul, hgtL_apply,pair_hgt,smul_eq_mul,mul_one,map_zero] at h₁
    simp only [map_sum,map_smul,horizL_apply,pair_horiz,map_zero] at h₂
    refine h s w h₁ ?_
    rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s w v h₁ (0 : Rn n),
      Finset.weightedVSubOfPoint_apply]
    simpa using h₂
  · intro h s w hw he
    rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s w v hw (0 : Rn n),
      Finset.weightedVSubOfPoint_apply] at he
    simp only [vsub_eq_sub,sub_zero] at he
    apply h
    let p := ∑ i ∈ s, w i • pair 1 (v i)
    change p = 0
    have h₁ : hgtL p = 0 := by simp only [p,map_sum,map_smul,hgtL_apply,pair_hgt,smul_eq_mul,mul_one,hw]
    have h₂ : horizL p = 0 := by simpa only [p,map_sum,map_smul,horizL_apply,pair_horiz] using he
    change hgt p = 0 at h₁
    change horiz p = 0 at h₂
    rw [← hgt_horiz_pair p,h₁,h₂,pair_zero]

theorem sum_coords (b : Basis (Fin (n+1)) ℝ (LiftSpace n)) (x : LiftSpace n) :
    ∑ i, b.equivFun x i • b i = x := by
  simpa only [Basis.equivFun_apply] using b.sum_repr x

namespace Body

lemma exists_basis_of_simplex {K : Body n} (hK : IsSimplex (K:Set (Rn n))) :
    ∃ b : Basis (Fin (n+1)) ℝ (LiftSpace n),
      (∀ i, hgt (b i) = 1) ∧ K.cone = orthant b := by
  rcases hK with ⟨v,hi,hv⟩
  have hvK (i) : v i ∈ K := by
    change v i ∈ (K:Set (Rn n))
    exact hv ▸ subset_convexHull ℝ _ (mem_range_self i)
  let vs := fun i => pair 1 (v i)
  have hd := (independence_lift v).mp hi
  have hf : Fintype.card (Fin (n+1)) = finrank ℝ (LiftSpace n) := by simp [lift_finrank]
  let b := basisOfLinearIndependentOfCardEqFinrank' vs hd hf
  have hbi (i) : b i = vs i := congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' ..) i
  refine ⟨b, fun i => by rw [hbi]; rfl,?_⟩
  let S := {x : Rn n | pair 1 x ∈ orthant b}
  have hKs : (K : Set (Rn n)) ⊆ S := by
    rw [hv]
    apply convexHull_min
    · rintro x ⟨i,rfl⟩
      change vs i ∈ orthant b
      rw [← hbi]
      exact basis_mem_orthant _ _
    · intro x hx y hy a a' ha ha' haa
      change pair 1 (a • x + a' • y) ∈ orthant b
      have he : a • pair 1 x + a' • pair 1 y = pair 1 (a • x + a' • y) := calc
        _ = pair (a*1+a'*1) (a • x + a' • y) := rfl
        _ = _ := by rw [mul_one,mul_one,haa]
      rw [← he]; apply (orthant b).convex _ _ ha ha' haa <;> assumption
  ext x
  constructor
  · rw [← hgt_horiz_pair x]
    intro hx
    obtain ⟨hu,y,hy,he⟩ := (Body.pair_mem_cone ..).mp hx
    have hi : pair 1 y ∈ orthant b := hKs hy
    have hh := (orthant b).smul_mem hi hu
    rw [he]; simpa only [smul_pair,mul_one] using hh
  · intro h
    have H : (∑ i, b.equivFun x i • b i) ∈ K.cone := by
      apply K.cone.sum_mem
      intro i _
      apply K.cone.smul_mem _ ((mem_orthant _).mp h i)
      rw [hbi]
      have he := hvK i
      simp [vs,he]
    rwa [sum_coords] at H

theorem simplex_of_linearOrthant {K : Body n} (h : IsLinearOrthant (n+1) K.cone) :
    IsSimplex (K:Set (Rn n)) := by
  obtain ⟨b,hb⟩ := h
  let a := fun i => hgt (b i)
  have hbi (i) : 0 ≤ a i ∧ ∃ x ∈ K, horiz (b i) = a i • x := (hb.symm ▸ basis_mem_orthant b i :
    b i ∈ K.cone)
  choose g hg hge using fun i => (hbi i).2
  have hv (i) : b i = pair (a i) (a i • g i) := by rw [← hge]; exact (hgt_horiz_pair _).symm
  have ha (i) : 0 < a i := lt_of_le_of_ne (hbi i).1 (by
    intro he; apply b.ne_zero i
    rw [hv,← he,zero_smul,pair_zero])
  have he (i) : (a i)⁻¹ • b i = pair 1 (g i) := calc
    _ = (a i)⁻¹ • pair (a i) (a i • g i) := congrArg _ (hv _)
    _ = _ := by simp [smul_pair, (ha i).ne']
  have hd : AffineIndependent ℝ g := by
    rw [independence_lift]
    let u : Fin (n+1) → ℝˣ := fun i => Units.mk0 _ (inv_ne_zero (ha i).ne')
    simp_rw [← he]
    exact b.linearIndependent.units_smul u
  refine ⟨g,hd, le_antisymm ?_ (convexHull_min (range_subset_iff.mpr hg) K.convex)⟩
  intro x hx
  let q := pair 1 x
  have hh : q ∈ orthant b := by
    rw [← hb, pair_mem_cone]
    exact ⟨zero_le_one,x,hx,(one_smul _ x).symm⟩
  let c : Fin (n+1) → ℝ := fun i => b.equivFun q i * a i
  have hc (i) : 0 ≤ c i := mul_nonneg ((mem_orthant b).mp hh i) (ha i).le
  have hf := sum_coords b q
  have H₁ := congrArg hgtL hf
  have H₂ := congrArg horizL hf
  simp only [map_sum,map_smul,hgtL_apply,q,pair_hgt,smul_eq_mul] at H₁
  simp only [map_sum,map_smul,horizL_apply,hge,smul_smul,q,pair_horiz] at H₂
  exact mem_convexHull_of_exists_fintype c g (fun i => hc i)
    H₁ (fun i => mem_range_self i) H₂

end Body
end GeneralMahler

end

end OAI
