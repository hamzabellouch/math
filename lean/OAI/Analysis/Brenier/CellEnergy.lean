import OAI.Analysis.Brenier.Flux
import OAI.Analysis.Brenier.Laplacian

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem358

variable {ι F : Type*} [Fintype ι]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The connected mass Jacobian and the stationary moment estimate control the
intercept velocity.  The auxiliary solution of the mass equation is constructed
here; in particular no quantitative inverse-Jacobian bound is assumed. -/
theorem fixed_mass_intercept_energy_le
    (g : ι → ι → ℝ) (b : ι → ι → F)
    (hg : ∀ i j, g i j = g j i) (hb : ∀ i j, b i j = b j i)
    (hg0 : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m r : ι → ℝ) (v : ι → F) {k w : ℝ}
    (hm : ∀ i, 0 < m i) (hk : 0 ≤ k)
    (hmean : ∑ i, m i * r i = 0)
    (hfixed : ∀ i, CellLaplacian.apply g r i +
      (∑ j, inner ℝ (b i j) (v i - v j)) = 0)
    (hspeed : (∑ i, m i * ‖v i‖ ^ 2) ≤ w ^ 2)
    (hmoment : ∀ q : ι → ℝ,
      (∑ i, ‖∑ j, (q i - q j) • b i j‖ ^ 2 / m i) ≤
        k * ∑ i, (CellLaplacian.apply g q i) ^ 2 / m i) :
    (∑ i, m i * r i ^ 2) ≤ k * w ^ 2 := by
  obtain ⟨q, hq⟩ := CellLaplacian.exists_apply_eq_of_sum_eq_zero
    g hg hg0 G hG hpos (fun i => m i * r i) hmean
  have hdual := fixed_mass_flux_duality q r v g b hg hb hfixed
  have hdual' : (∑ i, m i * r i ^ 2) =
      -(∑ i, inner ℝ (v i) (∑ j, (q i - q j) • b i j)) := by
    calc
      (∑ i, m i * r i ^ 2) = ∑ i, r i * CellLaplacian.apply g q i := by
        rw [hq]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := hdual
  have hmoment' : (∑ i, ‖∑ j, (q i - q j) • b i j‖ ^ 2 / m i) ≤
      k * ∑ i, m i * r i ^ 2 := by
    convert hmoment q using 1
    rw [hq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    field_simp [(hm i).ne']
  simpa only [Finset.mem_univ, forall_const] using
    intercept_energy_le Finset.univ m r v (fun i => ∑ j, (q i - q j) • b i j)
      (fun i _ => hm i) hk hspeed hdual' hmoment'

/-- The exact universal moment constant yields the energy input used by the
finite affine potential-path estimate. -/
theorem fixed_mass_intercept_energy_le_162
    (g : ι → ι → ℝ) (b : ι → ι → F)
    (hg : ∀ i j, g i j = g j i) (hb : ∀ i j, b i j = b j i)
    (hg0 : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m r : ι → ℝ) (v : ι → F) {R w : ℝ}
    (hm : ∀ i, 0 < m i) (hmean : ∑ i, m i * r i = 0)
    (hfixed : ∀ i, CellLaplacian.apply g r i +
      (∑ j, inner ℝ (b i j) (v i - v j)) = 0)
    (hspeed : (∑ i, m i * ‖v i‖ ^ 2) ≤ w ^ 2)
    (hmoment : ∀ q : ι → ℝ,
      (∑ i, ‖∑ j, (q i - q j) • b i j‖ ^ 2 / m i) ≤
        162 * R ^ 2 * ∑ i, (CellLaplacian.apply g q i) ^ 2 / m i) :
    (∑ i, m i * r i ^ 2) ≤ 162 * R ^ 2 * w ^ 2 :=
  fixed_mass_intercept_energy_le g b hg hb hg0 G hG hpos m r v hm
    (by positivity) hmean hfixed hspeed hmoment

end Problem358

namespace Problem358.CellLaplacian

variable {ι V : Type*} [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The mass variation caused by motion of the sites, in face coordinates. -/
def siteFlux (b : ι → ι → V) (v : ι → V) (i : ι) : ℝ :=
  ∑ j, inner ℝ (b i j) (v i - v j)

/-- Symmetric face moments conserve total mass under every site motion. -/
theorem sum_siteFlux (b : ι → ι → V) (hb : ∀ i j, b i j = b j i)
    (v : ι → V) : ∑ i, siteFlux b v i = 0 := by
  simpa only [siteFlux, one_mul, sub_self, zero_smul, Finset.sum_const_zero,
    inner_zero_right] using Problem358.symmetric_flux_pairing (fun _ : ι => 1) v b hb

/-- Projection onto the zero-sum mass space does not change the site flux. -/
theorem zeroSumProjection_siteFlux (m : ι → ℝ) (hm : ∑ i, m i = 1)
    (b : ι → ι → V) (hb : ∀ i j, b i j = b j i) (v : ι → V) :
    (zeroSumProjection m hm (siteFlux b v) : ι → ℝ) = siteFlux b v :=
  zeroSumProjection_eq m hm _ (sum_siteFlux b hb v)

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The site partial derivative of the projected mass residual is exactly the
physical face flux.  This removes the projection introduced to type the
implicit-function equation in its zero-sum codomain. -/
theorem massResidual_site_derivative
    (m : ι → ℝ) (hm : ∑ i, m i = 1)
    {M : P × normalizedSpace m → (ι → ℝ)} {x : P × normalizedSpace m}
    {A : P × normalizedSpace m →L[ℝ] (ι → ℝ)}
    (hM : HasFDerivAt M A x)
    (b : ι → ι → V) (hb : ∀ i j, b i j = b j i)
    (v : ι → V) (p : P) (hsite : A (p, 0) = siteFlux b v) :
    (fderiv ℝ (massResidual m hm M) x (p, 0) : ι → ℝ) = siteFlux b v := by
  rw [(hasFDerivAt_massResidual m hm hM).fderiv]
  change (zeroSumProjection m hm (A (p, 0)) : ι → ℝ) = _
  rw [hsite]
  exact zeroSumProjection_siteFlux m hm b hb v

end Problem358.CellLaplacian

end

noncomputable section

open Filter
open scoped BigOperators Topology ContDiff

namespace Problem358.CellLaplacian

variable {ι V : Type*} [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The actual derivative of the normalized implicit intercept branch obeys the
uniform weighted energy bound.  The site partial derivative is identified by
the face formula; no derivative, normalization, or mass-equation condition on
the selected branch is assumed separately. -/
theorem deriv_normalized_solution_energy_le
    {n : ℕ∞ω} (hn : n ≠ 0)
    (g : ι → ι → ℝ) (b : ι → ι → V)
    (hg : ∀ i j, g i j = g j i) (hb : ∀ i j, b i j = b j i)
    (hg0 : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hmsum : ∑ i, m i = 1)
    (F : ℝ × normalizedSpace m → normalizedSpace (fun _ : ι => 1))
    (s : ℝ → normalizedSpace m) (t : ℝ)
    (hF : ContDiffAt ℝ n F (t, s t))
    (hA : fderiv ℝ F (t, s t) ∘L ContinuousLinearMap.inr ℝ ℝ (normalizedSpace m) =
      (normalizedEquiv g hg hg0 G hG hpos m hmsum).toContinuousLinearMap)
    (hzero : F (t, s t) = 0)
    (hunique : ∀ᶠ x in 𝓝 t, ∀ q, F (x, q) = 0 → q = s x)
    (v : ι → V) {k w : ℝ} (hk : 0 ≤ k)
    (hsite : ∀ i,
      (fderiv ℝ F (t, s t) (1, 0) : ι → ℝ) i =
        ∑ j, inner ℝ (b i j) (v i - v j))
    (hspeed : (∑ i, m i * ‖v i‖ ^ 2) ≤ w ^ 2)
    (hmoment : ∀ q : ι → ℝ,
      (∑ i, ‖∑ j, (q i - q j) • b i j‖ ^ 2 / m i) ≤
        k * ∑ i, (apply g q i) ^ 2 / m i) :
    (∑ i, m i * ((deriv s t : normalizedSpace m) : ι → ℝ) i ^ 2) ≤
      k * w ^ 2 := by
  have hlap := laplacian_deriv_normalized_solution hn g hg hg0 G hG hpos
    m hmsum F s t hF hA hzero hunique
  have hmean : ∑ i, m i * ((deriv s t : normalizedSpace m) : ι → ℝ) i = 0 :=
    (deriv s t).property
  apply Problem358.fixed_mass_intercept_energy_le g b hg hb hg0 G hG hpos
    m ((deriv s t : normalizedSpace m) : ι → ℝ) v hm hk hmean _ hspeed hmoment
  intro i
  rw [congrFun hlap i]
  simp only [Pi.neg_apply, hsite i, neg_add_cancel]

end Problem358.CellLaplacian

namespace Problem358.CellLaplacian

variable {ι V : Type*} [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Version of the intercept derivative-energy estimate for the ordinary
coordinate-valued mass map.  Both partial derivatives of the normalized
residual are identified here from the actual coordinate derivative. -/
theorem deriv_massResidual_solution_energy_le
    {n : ℕ∞ω} (hn : n ≠ 0)
    (g : ι → ι → ℝ) (b : ι → ι → V)
    (hg : ∀ i j, g i j = g j i) (hb : ∀ i j, b i j = b j i)
    (hg0 : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hmsum : ∑ i, m i = 1)
    (M : ℝ × normalizedSpace m → (ι → ℝ))
    (s : ℝ → normalizedSpace m) (t : ℝ)
    (hM : ContDiffAt ℝ n M (t, s t))
    (A : ℝ × normalizedSpace m →L[ℝ] (ι → ℝ))
    (hDM : HasFDerivAt M A (t, s t))
    (hA : ∀ q : normalizedSpace m, A (0, q) = apply g q)
    (hzero : massResidual m hmsum M (t, s t) = 0)
    (hunique : ∀ᶠ x in 𝓝 t, ∀ q, massResidual m hmsum M (x, q) = 0 → q = s x)
    (v : ι → V) {k w : ℝ} (hk : 0 ≤ k)
    (hsite : A (1, 0) = siteFlux b v)
    (hspeed : (∑ i, m i * ‖v i‖ ^ 2) ≤ w ^ 2)
    (hmoment : ∀ q : ι → ℝ,
      (∑ i, ‖∑ j, (q i - q j) • b i j‖ ^ 2 / m i) ≤
        k * ∑ i, (apply g q i) ^ 2 / m i) :
    (∑ i, m i * ((deriv s t : normalizedSpace m) : ι → ℝ) i ^ 2) ≤
      k * w ^ 2 := by
  apply deriv_normalized_solution_energy_le hn g b hg hb hg0 G hG hpos m hm hmsum
    (massResidual m hmsum M) s t (contDiffAt_massResidual m hmsum hM) _
    hzero hunique v hk _ hspeed hmoment
  · rw [(hasFDerivAt_massResidual m hmsum hDM).fderiv]
    exact massResidual_partial_eq g hg hg0 G hG hpos m hmsum A hA
  · intro i
    exact congrFun (massResidual_site_derivative m hmsum hDM b hb v 1 hsite) i

end Problem358.CellLaplacian

end

end OAI
