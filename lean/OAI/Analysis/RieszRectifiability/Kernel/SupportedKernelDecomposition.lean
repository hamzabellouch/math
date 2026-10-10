import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.SymmetricHeightKernel

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Filter

theorem supported_kernel_integral_decomposition {d : ℕ}
    (μ : Measure (Ambient d)) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (g : Ambient d → ℂ) (hgs : ∀ y ∈ sᶜ, g y = 0)
    (k : Ambient d × Ambient d → ℝ) (x : Ambient d)
    (hi : Integrable (fun y => k (x, y) • (g x - g y)) μ) :
    (∫ y, k (x, y) • (g x - g y) ∂μ) =
      (∫ y in s, k (x, y) • (g x - g y) ∂μ) +
        ∫ y in sᶜ, k (x, y) • g x ∂μ := by
  rw [← integral_add_compl hs hi]
  congr 1
  apply setIntegral_congr_fun hs.compl
  intro y hy
  dsimp only
  rw [hgs y hy, sub_zero]

theorem supported_kernel_integral_outside {d : ℕ}
    (μ : Measure (Ambient d)) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (g : Ambient d → ℂ) (hgs : ∀ y ∈ sᶜ, g y = 0)
    (k : Ambient d × Ambient d → ℝ) (x : Ambient d) (hx : x ∈ sᶜ)
    (hi : Integrable (fun y => k (x, y) • (g x - g y)) μ) :
    (∫ y, k (x, y) • (g x - g y) ∂μ) =
      -(∫ y in s, k (x, y) • g y ∂μ) := by
  rw [supported_kernel_integral_decomposition μ s hs g hgs k x hi, hgs x hx]
  simp only [Complex.real_smul, zero_sub, mul_neg, mul_zero, integral_zero, add_zero, integral_neg]

theorem supported_height_kernel_integral_decomposition {d : ℕ}
    (μ : Measure (Ambient d)) [SFinite μ]
    (s : Set (Ambient d)) (hs : MeasurableSet s)
    (w : Ambient d → ℝ) (g : Ambient d → ℂ) (hgs : ∀ y ∈ sᶜ, g y = 0)
    (k : Ambient d × Ambient d → ℝ)
    (hi : ∀ x, Integrable (fun y => k (x, y) • (g x - g y)) μ)
    (hL : Integrable (fun q : Ambient d × Ambient d =>
      w q.1 • (k q • (g q.1 - g q.2))) ((μ.restrict s).prod (μ.restrict s)))
    (hD : Integrable (fun q : Ambient d × Ambient d =>
      w q.1 • (k q • g q.1)) ((μ.restrict s).prod (μ.restrict sᶜ)))
    (hO : IntegrableOn (fun y => w y • (∫ x in s, k (y, x) • g x ∂μ)) sᶜ μ) :
    Integrable (fun x => w x • (∫ y, k (x, y) • (g x - g y) ∂μ)) μ ∧
      (∫ x, w x • (∫ y, k (x, y) • (g x - g y) ∂μ) ∂μ) =
        (∫ x in s, w x • (∫ y in s, k (x, y) • (g x - g y) ∂μ) ∂μ) +
        (∫ x in s, w x • (∫ y in sᶜ, k (x, y) • g x ∂μ) ∂μ) -
          ∫ y in sᶜ, w y • (∫ x in s, k (y, x) • g x ∂μ) ∂μ := by
  let T := fun x => w x • (∫ y, k (x, y) • (g x - g y) ∂μ)
  let L := fun x => w x • (∫ y in s, k (x, y) • (g x - g y) ∂μ)
  let D := fun x => w x • (∫ y in sᶜ, k (x, y) • g x ∂μ)
  let O := fun y => w y • (∫ x in s, k (y, x) • g x ∂μ)
  have hLI : IntegrableOn L s μ := by
    apply hL.integral_prod_left.congr
    exact Eventually.of_forall fun x => integral_smul (w x) _
  have hDI : IntegrableOn D s μ := by
    apply hD.integral_prod_left.congr
    exact Eventually.of_forall fun x => integral_smul (w x) _
  have hTin : T =ᵐ[μ.restrict s] fun x => L x + D x := by
    apply Eventually.of_forall
    intro x
    dsimp only [T, L, D]
    rw [supported_kernel_integral_decomposition μ s hs g hgs k x (hi x)]
    exact smul_add (w x) _ _
  have hTout : T =ᵐ[μ.restrict sᶜ] fun x => -(O x) := by
    filter_upwards [ae_restrict_mem hs.compl] with x hx
    dsimp only [T, O]
    rw [supported_kernel_integral_outside μ s hs g hgs k x hx (hi x)]
    exact smul_neg (w x) _
  have hTI : IntegrableOn T s μ := (hLI.add hDI).congr hTin.symm
  have hTE : IntegrableOn T sᶜ μ := hO.neg.congr hTout.symm
  have hT : Integrable T μ := by
    simpa only [union_compl_self, integrableOn_univ] using! hTI.union hTE
  refine ⟨hT, ?_⟩
  change (∫ x, T x ∂μ) = (∫ x in s, L x ∂μ) + (∫ x in s, D x ∂μ) - ∫ x in sᶜ, O x ∂μ
  rw [← integral_add_compl hs hT, integral_congr_ae hTin, integral_congr_ae hTout,
    integral_add hLI hDI, integral_neg, sub_eq_add_neg]

end

end RieszRectifiability

end OAI
