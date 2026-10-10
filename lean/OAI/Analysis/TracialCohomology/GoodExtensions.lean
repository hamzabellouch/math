import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.FreshBounds

namespace OAI

/-! Good extensions for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaPatching
attribute [local instance] Classical.propDecidable
universe u
variable {C B G : Type*} [Group G]
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1 in
theorem good_add (hII : PopaTypeII.NoAbelianCorners M)
    (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → G) (b0 : B) (hb0 : γ b0=1)
    (L : ℕ) (ε : ℕ → ℝ) (hε : ∀ n, 0≤ε n) (hmono : Monotone ε)
    (v : Rep G M) (hv : Good e τ hτ htr hfaith a γ L ε v)
    {p q : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) (hpv : p=1-v.support)
    (hEp : Homogeneous e τ hτ htr hfaith p)
    (hq : IsStarProjection q) (hq0 : q ≠ 0) (hEq : Homogeneous e τ hτ htr hfaith q)
    (w : Rep G M) (hw : w.support=q) (hvw : v.support*w.support=0)
    (δ θ : ℝ) (hδ : 0<δ) (hpδ : δ≤(τ p).re) (hθ : 0≤θ)
    (hsmall : (τ q).re < (τ p).re/((2:ℝ)^L+1))
    (hstep : ∀ k, 1≤k → k≤L → (2:ℝ)^L*(2*ε (k-1)/δ+(L:ℝ)*θ)≤ε k)
    (hkill : ∀ bs : List B, bs.length≤L → (bs.map γ).prod ≠ 1 → average e τ hτ htr hfaith (w ((bs.map γ).prod))=0)
    (he : ∀ l : List (Letter C B), l.length≤L →
      ‖(PopaCorner.trace hq τ).toPreGNS (PopaCorner.compress hq (evaluate a γ v l)-
        PopaCorner.compress hq (cornerCoefficient e τ hτ htr hfaith hp (evaluate a γ v l)))‖≤θ) :
    Good e τ hτ htr hfaith a γ L ε (v.add w hvw) := by
  classical
  refine ⟨?_,fun l hl hd => ?_⟩
  · rw [Rep.add_support,hw]
    exact homogeneous_add e τ hτ htr hfaith h1 hv.1 hEq
  have hk : 1≤l.length := by
    by_contra hh
    have he : l=[] := List.length_eq_zero_iff.mp (by omega)
    exact hd (by rw [he]; rfl)
  let H := 2*ε (l.length-1)/δ+(L:ℝ)*θ
  let N : ℝ := 2^L
  let A : ℝ := (τ q).re/(τ p).re
  let c : List (Mark C B) → ℝ := fun m => if identitySingleton γ (freshs m) then A else 0
  have ht : 0<(τ p).re := lt_of_lt_of_le hδ hpδ
  have hqpos : 0<(τ q).re := HochschildDiffuse.projection_trace_pos τ hfaith hq hq0
  have hN : 0<N := pow_pos (by norm_num) _
  have hA : 0≤A := div_nonneg hqpos.le ht.le
  have hAeq : A*(τ p).re=(τ q).re := div_mul_cancel₀ _ ht.ne'
  have hNA : N*A≤1 := by
    have hh : (τ q).re*(N+1)<(τ p).re := (lt_div_iff₀ (by positivity)).mp hsmall
    have hh' : (N*A)*(τ p).re≤(τ p).re := by nlinarith
    nlinarith
  have hc0 (m) (_ : m ∈ newVariants l) : 0≤c m := by dsimp [c]; split <;> positivity
  have hcA (m) (_ : m ∈ newVariants l) : c m≤A := by
    dsimp [c]
    split
    · exact le_rfl
    · exact hA
  have hlen : ((newVariants l).length:ℝ)≤N := by
    dsimp [N]
    exact_mod_cast (newVariants_length_le l).trans (Nat.pow_le_pow_right (by decide) hl)
  have hc1 : ((newVariants l).map c).sum≤1 := by
    calc
      _ ≤ ((newVariants l).map (fun _ => A)).sum := List.sum_le_sum hcA
      _ = ((newVariants l).length:ℝ)*A := by simp
      _ ≤ N*A := mul_le_mul_of_nonneg_right hlen hA
      _ ≤ 1 := hNA
  have hH : 0≤H := by
    exact add_nonneg (div_nonneg (mul_nonneg (by norm_num) (hε _)) hδ.le)
      (mul_nonneg (Nat.cast_nonneg _) hθ)
  have hb (m) (hm : m ∈ newVariants l) :
      ‖τ.toPreGNS (average e τ hτ htr hfaith (markedEval a γ v w m))+c m •
        τ.toPreGNS (average e τ hτ htr hfaith (evaluate a γ v l))‖≤H*(τ q).re := by
    have hm' := mem_newVariants l m hm
    have her := erase_variant l m hm'.1
    have hmlen : m.length=l.length := by
      have hh := congrArg List.length her
      simpa only [List.length_map] using hh
    obtain ⟨b,hb,hf,hbl,hd',htrace,hold⟩ := cyclic_blocks (average e τ hτ htr hfaith) (average_trace e τ hτ htr hfaith h1) a γ v w m hm'.2 (by rwa [her])
    have hh := all_blocks_bound e τ hτ htr hfaith h1 hII a ha γ b0 hb0 L ε hε hmono v hv
      hp hp0 hpv hEp hq hq0 hEq w hw δ θ hδ hpδ hθ hkill he b hb (by rwa [hbl,hmlen]) hd'
    rw [hf,hbl,hmlen,←htrace,←hold,her] at hh
    simpa only [map_add,preGNS_real_smul τ] using hh
  have hsum := patch_sum_bound (newVariants l) (τ.toPreGNS (average e τ hτ htr hfaith (evaluate a γ v l)))
    (fun m => τ.toPreGNS (average e τ hτ htr hfaith (markedEval a γ v w m))) c (ε l.length) (Rep.rank τ v) (τ q).re H
    (hε _) (rank_nonneg τ v) hqpos.le hH hc0 hc1 (hv.2 l hl hd) hb
    ((mul_le_mul_of_nonneg_right hlen hH).trans (hstep l.length hk hl))
  have hrank : Rep.rank τ (v.add w hvw)=Rep.rank τ v+(τ q).re := by
    simp only [Rep.rank,Rep.add_support,hw,map_add,Complex.add_re]
  rw [hrank,evaluate_add_new_expansion]
  change ‖τ.toPreGNS (expectation e τ hτ htr hfaith h1 (_+_))‖≤_
  rw [map_add,map_add,map_list_sum,map_list_sum]
  simpa only [List.map_map,Function.comp_def,expectation_apply] using hsum
end PopaCenter

open scoped ComplexOrder
namespace PopaPatching
variable {C B G M : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

theorem good_add (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → G) (b0 : B) (hb0 : γ b0=1)
    (L : ℕ) (ε : ℕ → ℝ) (hε : ∀ n, 0≤ε n) (hmono : Monotone ε)
    (v : Rep G M) (hv : Good τ a γ L ε v)
    {p q : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) (hpv : p=1-v.support)
    (hq : IsStarProjection q) (hq0 : q ≠ 0) (w : Rep G M) (hw : w.support=q)
    (hvw : v.support*w.support=0)
    (δ θ : ℝ) (hδ : 0<δ) (hpδ : δ≤(τ p).re) (hθ : 0≤θ)
    (hsmall : (τ q).re < (τ p).re/((2:ℝ)^L+1))
    (hstep : ∀ k, 1≤k → k≤L → (2:ℝ)^L*(2*ε (k-1)/δ+(L:ℝ)*θ)≤ε k)
    (hkill : ∀ bs : List B, bs.length≤L → (bs.map γ).prod ≠ 1 → τ (w ((bs.map γ).prod))=0)
    (he : ∀ l : List (Letter C B), l.length≤L →
      ‖(PopaCorner.trace hq τ).toPreGNS (PopaCorner.compress hq (evaluate a γ v l)-
        (PopaCorner.trace hp τ (PopaCorner.compress hp (evaluate a γ v l))) • 1)‖≤θ) :
    Good τ a γ L ε (v.add w hvw) := by
  classical
  intro l hl hd
  have hk : 1≤l.length := by
    by_contra hh
    have he : l=[] := List.length_eq_zero_iff.mp (by omega)
    exact hd (by rw [he]; rfl)
  let H := 2*ε (l.length-1)/δ+(L:ℝ)*θ
  let N : ℝ := 2^L
  let A : ℝ := (τ q).re/(τ p).re
  let c : List (Mark C B) → ℝ := fun m => if identitySingleton γ (freshs m) then A else 0
  have ht : 0<(τ p).re := lt_of_lt_of_le hδ hpδ
  have hqpos : 0<(τ q).re := HochschildDiffuse.projection_trace_pos τ hfaith hq hq0
  have hN : 0<N := pow_pos (by norm_num) _
  have hA : 0≤A := div_nonneg hqpos.le ht.le
  have hAeq : A*(τ p).re=(τ q).re := div_mul_cancel₀ _ ht.ne'
  have hNA : N*A≤1 := by
    have hh : (τ q).re*(N+1)<(τ p).re := (lt_div_iff₀ (by positivity)).mp hsmall
    have hh' : (N*A)*(τ p).re≤(τ p).re := by nlinarith
    nlinarith
  have hc0 (m) (_ : m ∈ newVariants l) : 0≤c m := by dsimp [c]; split <;> positivity
  have hcA (m) (_ : m ∈ newVariants l) : c m≤A := by
    dsimp [c]
    split
    · exact le_rfl
    · exact hA
  have hlen : ((newVariants l).length:ℝ)≤N := by
    dsimp [N]
    exact_mod_cast (newVariants_length_le l).trans (Nat.pow_le_pow_right (by decide) hl)
  have hc1 : ((newVariants l).map c).sum≤1 := by
    calc
      _ ≤ ((newVariants l).map (fun _ => A)).sum := List.sum_le_sum hcA
      _ = ((newVariants l).length:ℝ)*A := by simp
      _ ≤ N*A := mul_le_mul_of_nonneg_right hlen hA
      _ ≤ 1 := hNA
  have hH : 0≤H := by
    exact add_nonneg (div_nonneg (mul_nonneg (by norm_num) (hε _)) hδ.le)
      (mul_nonneg (Nat.cast_nonneg _) hθ)
  have hb (m) (hm : m ∈ newVariants l) :
      ‖τ (markedEval a γ v w m)+(c m:ℂ)*τ (evaluate a γ v l)‖≤H*(τ q).re := by
    have hm' := mem_newVariants l m hm
    have her := erase_variant l m hm'.1
    have hmlen : m.length=l.length := by
      have hh := congrArg List.length her
      simpa only [List.length_map] using hh
    obtain ⟨b,hb,hf,hbl,hd',htrace,hold⟩ := cyclic_blocks τ htr a γ v w m hm'.2 (by rwa [her])
    have hh := all_blocks_bound τ htr hfaith h1 a ha γ b0 hb0 L ε hε hmono v hv
      hp hp0 hpv hq hq0 w hw δ θ hδ hpδ hθ hkill he b hb (by rwa [hbl,hmlen]) hd'
    rw [hf,hbl,hmlen,←htrace,←hold,her] at hh
    exact hh
  have hsum := patch_sum_bound (newVariants l) (τ (evaluate a γ v l))
    (fun m => τ (markedEval a γ v w m)) c (ε l.length) (Rep.rank τ v) (τ q).re H
    (hε _) (rank_nonneg τ v) hqpos.le hH hc0 hc1 (hv l hl hd) hb
    ((mul_le_mul_of_nonneg_right hlen hH).trans (hstep l.length hk hl))
  have hrank : Rep.rank τ (v.add w hvw)=Rep.rank τ v+(τ q).re := by
    simp only [Rep.rank,Rep.add_support,hw,map_add,Complex.add_re]
  rw [hrank,evaluate_add_new_expansion,map_add,map_list_sum]
  simpa only [List.map_map,Function.comp_def] using hsum
end PopaPatching

end

end OAI
