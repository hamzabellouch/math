import OAI.Probability.InvariantIsing.Cavity.CavityRDerivative
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteField

namespace OAI

/-! The finite field path reconstructed by the cavity covariance.
Its covariance density has the continuous right-derivative value at zero. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

def cavityFieldDensity (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (p : OverlapPath) (r : ℝ) : ℝ :=
  cavityRDerivative rho lam hrho hsum (deficit p r)

def cavityFieldPrimitive (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (p : OverlapPath) (r : ℝ) : ℝ :=
  ∫ u in 0..r, cavityFieldDensity rho lam hrho hsum p u

def cavityFieldDiagonal (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (p : OverlapPath) : ℝ :=
  cavityFieldPrimitive rho lam hrho hsum p 1

lemma continuous_cavityFieldDensity (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (p : OverlapPath) :
    Continuous (cavityFieldDensity rho lam hrho hsum p) :=
  (continuous_cavityRDerivative rho lam hrho hsum).comp (continuous_deficit p)

lemma cavityFieldPrimitive_nonneg (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (p : OverlapPath) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ cavityFieldPrimitive rho lam hrho hsum p r :=
  intervalIntegral.integral_nonneg_of_forall hr
    (fun _ => cavityRDerivative_nonneg rho lam hrho hsum _)

lemma cavityFieldPrimitive_mono (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (p : OverlapPath) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    cavityFieldPrimitive rho lam hrho hsum p a ≤ cavityFieldPrimitive rho lam hrho hsum p b :=
  intervalIntegral.integral_mono_interval le_rfl ha hab
    (ae_of_all _ (fun _ => cavityRDerivative_nonneg rho lam hrho hsum _))
    ((continuous_cavityFieldDensity rho lam hrho hsum p).intervalIntegrable 0 b)

lemma cavityFieldPrimitive_sub (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (p : OverlapPath) (a b : ℝ) :
    cavityFieldPrimitive rho lam hrho hsum p b - cavityFieldPrimitive rho lam hrho hsum p a =
      ∫ r in a..b, cavityFieldDensity rho lam hrho hsum p r := by
  have hc := continuous_cavityFieldDensity rho lam hrho hsum p
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a b)
  unfold cavityFieldPrimitive
  linarith

def cavityFieldStep (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (p : OverlapPath)
    {n : ℕ} (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q) (hq0 : ∀ i, 0 ≤ q i) : FieldStep where
  depth := n
  cut := cut
  ordered_cut := hcut
  first := hfirst
  last := hlast
  height := fun i => cavityFieldPrimitive rho lam hrho hsum p (q i)
  nonneg := fun i => cavityFieldPrimitive_nonneg rho lam hrho hsum p (hq0 i)
  ordered_height := fun i _j hij => cavityFieldPrimitive_mono rho lam hrho hsum p (hq0 i) (hq hij)

lemma cavityFieldStep_on_cell (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (p : OverlapPath)
    {n : ℕ} (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q) (hq0 : ∀ i, 0 ≤ q i)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (i : Fin (n + 1)) {s : ℝ} (hs : s ∈ Ioo (cut i.castSucc) (cut i.succ)) :
    fieldFunction (cavityFieldStep rho lam hrho hsum p cut hcut hfirst hlast q hq hq0) s =
      cavityFieldPrimitive rho lam hrho hsum p (p s) := by
  change IsingPerceptron.finiteStepFunction cut
    (fun j => cavityFieldPrimitive rho lam hrho hsum p (q j)) s = _
  rw [IsingPerceptron.finiteStepFunction_on_cell hcut _ hs, hp i s hs]

end InvariantIsing

end

end OAI
