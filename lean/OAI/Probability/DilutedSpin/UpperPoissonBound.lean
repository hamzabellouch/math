import OAI.Probability.DilutedSpin.PoissonReplacement
import OAI.Probability.DilutedSpin.UpperCountLocal

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory KernelTower
open scoped NNReal
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

lemma upperPoissonCount_bound (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ d,0 ≤ m d)
    (hstrict : ∀ d : Fin n,0 < m d.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (j : Fin p) (f : FinitePath Ω n → ℝ) (r : ℝ≥0)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᵐ a ∂M.disorder.toMeasure,‖a.1‖≤C) :
    (∫ k,upperCountMean M T Q U V x (fun d => m d.succ) j f k 0 ∂poissonMeasure (r/p))+
      (r:ℝ)*(((p-1:ℕ):ℝ)/p)*(∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure) ≤
    ∫ l,upperCountMean M T Q U V x (fun d => m d.succ) j f 0 l ∂poissonMeasure r := by
  have hp : 0 < p := by have := hM.arity; omega
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  have hpR : (p:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hp
  let e := ∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure
  have hh := poisson_count_replacement r p
    (upperCountMean M T Q U V x (fun d => m d.succ) j f)
    ((((p-1:ℕ):ℝ)/p)*e) hC0
    (fun k l => upperCountMean_bound M hC T Q U V x _ hstrict j f k l
      (fun y => norm_le_pi_norm f y))
    (fun k l => ?_)
  · simpa only [mul_assoc] using hh
  · have h := upperCountMean_replacement M hM T Q U V x m hm hpos hstrict hroot hend j f k l hC
    convert h using 1
    dsimp only [e]
    field_simp

end DilutedSpinGlass.PrescribedTree

end

end OAI
