import Mathlib
import OAI.Probability.Ballisticity.Crossings.FirstHitUpward

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma coordinate_raw_kernel_comp_le {d : ℕ} (e : Direction d) (k m : ℕ)
    (ω : Environment d) (x : Lattice d) (U : Set (Lattice d)) :
    (∫⁻ y, hitKernel (Strip (realPosition (step e)) y m) (Upper (realPosition (step e)) y m) (ω,y) U
      ∂hitKernel (Strip (realPosition (step e)) x k) (Upper (realPosition (step e)) x k) (ω,x)) ≤
      hitKernel (Strip (realPosition (step e)) x (k+m)) (Upper (realPosition (step e)) x (k+m)) (ω,x) U := by
  let ℓ := realPosition (step e)
  let b := dot (realPosition x) ℓ+(k:ℝ)
  let c := dot (realPosition x) ℓ+((k+m:ℕ):ℝ)
  let S₂ : Set (Lattice d) := {y | b ≤ dot (realPosition y) ℓ ∧ dot (realPosition y) ℓ < c}
  let T₂ : Set (Lattice d) := {y | c ≤ dot (realPosition y) ℓ}
  have he : (∫⁻ y, hitKernel (Strip ℓ y m) (Upper ℓ y m) (ω,y) U
      ∂hitKernel (Strip ℓ x k) (Upper ℓ x k) (ω,x)) =
      ∫⁻ y, hitKernel S₂ T₂ (ω,y) U ∂hitKernel (Strip ℓ x k) (Upper ℓ x k) (ω,x) := by
    apply lintegral_congr_ae
    filter_upwards [coordinate_hitKernel_supported e x k ω] with y hy
    have hproj : dot (realPosition y) ℓ=b := by
      dsimp [ℓ,b]
      rw [signedHeight_projection,signedHeight_projection]
      exact_mod_cast hy
    have hS : Strip ℓ y m=S₂ := by
      ext z
      simp only [Strip,Set.mem_ofPred_eq,S₂,hproj,b,c,Nat.cast_add,add_assoc]
    have hT : Upper ℓ y m=T₂ := by
      ext z
      simp only [Upper,Set.mem_ofPred_eq,T₂,hproj,b,c,Nat.cast_add,add_assoc]
    rw [hS,hT]
  rw [he]
  have hd : Disjoint S₂ T₂ := Set.disjoint_left.mpr (fun y hy hz => (not_lt_of_ge hz) hy.2)
  have hT : T₂=Upper ℓ x (k+m) := by
    simp only [T₂,Upper,c,Nat.cast_add]
  have hk : Strip ℓ x k ⊆ Strip ℓ x (k+m) := by
    intro y hy
    refine ⟨hy.1,?_⟩
    dsimp [Strip] at hy ⊢
    have := Nat.cast_nonneg (α := ℝ) m
    linarith [hy.2]
  have hm : S₂ ⊆ Strip ℓ x (k+m) := by
    intro y hy
    refine ⟨?_,by simpa only [c,Nat.cast_add] using hy.2⟩
    dsimp [S₂,b,Strip] at hy ⊢
    have := Nat.cast_nonneg (α := ℝ) k
    linarith [hy.1]
  have hh := hitKernel_comp_le ω x (disjoint_strip_upper ℓ x k) hd
    (hT ▸ disjoint_strip_upper ℓ x (k+m)) hk hm U
  simpa only [hT] using hh
end DirectionalTransience

end

end

end OAI
