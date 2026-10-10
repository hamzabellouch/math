import OAI.Probability.ProjectionMoments.CapDomination

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma normalized_strong_moment {ν : Measure E} [IsFiniteMeasure ν] {a : ℝ}
    (hν : NoiselessRegression.HasLocalMassBound ν a)
    (hs : ν.support ⊆ Metric.closedBall 0 1) (hmass : ν Set.univ ≤ 1)
    {k n : ℕ} (hk : 1 ≤ k) (hkd : k ≤ Module.finrank ℝ E)
    (hdk : Module.finrank ℝ E ≤ 32*k) (ha : a ≤ Module.finrank ℝ E)
    (hmargin : (n:ℝ)+k ≤ a) {u : Fin k → E} (hu : Orthonormal ℝ u)
    (hac : ∀ᵐ A ∂frameLaw u, ν.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ))) :
    (∫⁻ X, ∫⁻ y, normalizedDensity ν k u (X,y)^(n+1) ∂unitBallLaw k
      ∂Measure.pi (fun _ => stdGaussian E)) ≤
      ENNReal.ofReal ((16384:ℝ)^(Module.finrank ℝ E*(n+1))) := by
  apply (normalizedMoment_le ν hkd hu n).trans
  apply (mul_le_mul' le_rfl (frame_moment_unit hν hs hmass (by omega) ha hkd hmargin u hu hac)).trans
  simpa only [one_pow, ENNReal.ofReal_one, one_mul, max_self, mul_one] using
    normalized_cost (Module.finrank ℝ E) k n hk hkd hdk 1 one_pos

lemma rescaled_kernel_identity {μ : Measure E} [IsFiniteMeasure μ] {K a : ℝ}
    (hK : 0 < K) (c : E) {r : ℝ} (hr : 0 < r)
    (hs : μ.support ⊆ Metric.closedBall c r) {k : ℕ} (hk : k ≤ Module.finrank ℝ E)
    {Q : (Fin k → E) × Label k → ℝ≥0∞} (hQ : Measurable Q)
    {u : Fin k → E} (hu : Orthonormal ℝ u)
    (hac : ∀ X, (normalizedRescale μ K a c r).map (rowMap (polarRows u X)) ≪
      (volume : Measure (Label k))) :
    (∫⁻ s, capKernelValue Q s ∂μ) =
      ENNReal.ofReal (K*r^a) * ∫⁻ X, ∫⁻ y,
        normalizedDensity (normalizedRescale μ K a c r) k u (X,y) *
          Q (X,capReferenceLabel c r X y) ∂unitBallLaw k ∂Measure.pi (fun _ => stdGaussian E) := by
  let ν := normalizedRescale μ K a c r
  let : IsFiniteMeasure ν := normalizedRescale_finite μ K a c r (by positivity)
  have hsν : ν.support ⊆ Metric.closedBall 0 1 := normalizedRescale_support K a c hr hs
  have he (X : Fin k → E) (hX : LinearIndependent ℝ X) :
      (∫⁻ s, Q (X,rowMap X s) ∂μ) =
      ENNReal.ofReal (K*r^a) * ∫⁻ y, normalizedDensity ν k u (X,y)*
        Q (X,capReferenceLabel c r X y) ∂unitBallLaw k := by
    have hid := lintegral_withDensity_eq_lintegral_mul (unitBallLaw k)
      (show Measurable (fun y => normalizedDensity ν k u (X,y)) by fun_prop)
      (show Measurable (fun y => Q (X,capReferenceLabel c r X y)) by fun_prop)
    simp only [Pi.mul_apply] at hid
    rw [← hid,normalizedDensity_unitBall ν hu hsν X (hac X),lintegral_map (by fun_prop) (by fun_prop)]
    have hrec : ENNReal.ofReal (K*r^a) • ν.map (dilate c r) = μ := normalizedRescale_recover μ K a hK c hr
    calc
      _ = ∫⁻ s, Q (X,rowMap X s) ∂(ENNReal.ofReal (K*r^a) • ν.map (dilate c r)) := by rw [hrec]
      _ = _ := by
        rw [lintegral_smul_measure,lintegral_map (by fun_prop) (measurable_dilate c r)]
        congr 1
        apply lintegral_congr
        intro s
        rw [capReferenceLabel, ← polar_label_identity hX u c s r]
  change (∫⁻ s, ∫⁻ X, Q (X,rowMap X s) ∂Measure.pi (fun _ => stdGaussian E) ∂μ) = _
  rw [lintegral_lintegral_swap (show AEMeasurable (fun z : E × (Fin k → E) => Q (z.2,rowMap z.2 z.1)) _ by
    apply Measurable.aemeasurable; exact hQ.comp (measurable_snd.prodMk (by simp only [rowMap_apply]; fun_prop)))]
  rw [← lintegral_const_mul _ (by fun_prop)]
  exact lintegral_congr_ae (by filter_upwards [gaussian_rows_ae_linearIndependent k hk] with X hX; exact he X hX)

lemma localized_fractional_kernel_bound {μ : Measure E} [IsFiniteMeasure μ] {K a : ℝ}
    (hlocal : AllBallMass μ K a) (hK : 0 ≤ K)
    (c : E) {r : ℝ} (hr : 0 < r) (hs : μ.support ⊆ Metric.closedBall c r)
    {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) (hkd : k ≤ Module.finrank ℝ E)
    (hdk : Module.finrank ℝ E ≤ 32*k) (ha : a ≤ Module.finrank ℝ E)
    (hmargin : (n:ℝ)+k ≤ a)
    {Q : (Fin k → E) × Label k → ℝ≥0∞} (hQ : Measurable Q) (hQ1 : ∀ z, Q z ≤ 1)
    {u : Fin k → E} (hu : Orthonormal ℝ u)
    (hac : ∀ A, Orthonormal ℝ A → μ.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ))) :
    (∫⁻ s, capKernelValue Q s ∂μ) ≤
      ENNReal.ofReal ((16384:ℝ)^Module.finrank ℝ E) * ENNReal.ofReal (K*r^a) *
        (capReference Q c r)^(1-1/((n:ℝ)+1)) := by
  rcases eq_or_lt_of_le hK with hK | hK
  · have hz := measure_eq_zero_of_allBall_zero (hK ▸ hlocal) c hr hs
    subst μ
    simp
  let ν := normalizedRescale μ K a c r
  let : IsFiniteMeasure ν := normalizedRescale_finite μ K a c r (by positivity)
  have hsν : ν.support ⊆ Metric.closedBall 0 1 := normalizedRescale_support K a c hr hs
  have hmass : ν Set.univ ≤ 1 := normalizedRescale_mass hlocal hK c hr hs
  have hacν (A : Fin k → E) (hA : Orthonormal ℝ A) :
      ν.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ)) := by
    change (normalizedRescale μ K a c r).map (coordinateMap A) ≪ _
    rw [normalizedRescale, Measure.map_smul _ (by fun_prop)]
    exact Measure.smul_absolutelyContinuous.trans (rescaled_projection_ac A c hr (hac A hA))
  have hacX (X : Fin k → E) : ν.map (rowMap (polarRows u X)) ≪ (volume : Measure (Label k)) :=
    (rowMap_ac_iff _).mpr (hacν _ (polarRows_orthonormal hu X))
  have hm := normalized_strong_moment (normalizedRescale_local hlocal hK c hr) hsν hmass hk hkd hdk ha hmargin hu
    (polar_ac_to_frame ν hkd hu (Filter.Eventually.of_forall hacX))
  let γ := Measure.pi (fun _ : Fin k => stdGaussian E)
  let F : (Fin k → E) × Label k → ℝ≥0∞ := fun z => Q (z.1,capReferenceLabel c r z.1 z.2)
  have hF : Measurable F := hQ.comp (measurable_fst.prodMk (measurable_capReferenceLabel c r))
  have hp : (1:ℝ) < (n:ℝ)+1 := by exact_mod_cast (show 1 < n+1 by omega)
  have hnorm : (∫⁻ z, normalizedDensity ν k u z ^ ((n:ℝ)+1) ∂γ.prod (unitBallLaw k)) ≤
      ENNReal.ofReal ((16384:ℝ)^Module.finrank ℝ E)^(n+1) := by
    rw [lintegral_prod _ (by fun_prop)]
    simpa only [←Nat.cast_add_one,ENNReal.rpow_natCast,pow_mul,ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ 16384),
      ENNReal.ofReal_pow (by positivity : 0 ≤ (16384:ℝ)^Module.finrank ℝ E)] using hm
  have hb := holder_bounded_kernel (γ.prod (unitBallLaw k))
    (measurable_normalizedDensity ν k u) hF (fun z => hQ1 _) hp hnorm
  have hroot : (ENNReal.ofReal ((16384:ℝ)^Module.finrank ℝ E)^(n+1))^(1/((n:ℝ)+1)) ≤
      ENNReal.ofReal ((16384:ℝ)^Module.finrank ℝ E) := by
    simpa only [Nat.cast_add,Nat.cast_one] using ennreal_root_bound (q := n+1) (by omega)
      (by positivity : 0 ≤ (16384:ℝ)^Module.finrank ℝ E) le_rfl
  have hb' := hb.trans (mul_le_mul' hroot le_rfl)
  rw [lintegral_prod _ (by fun_prop),lintegral_prod _ (by fun_prop)] at hb'
  rw [rescaled_kernel_identity hK c hr hs hkd hQ hu hacX]
  apply (mul_le_mul' le_rfl hb').trans_eq
  dsimp only [F,γ,capReference]
  ring

lemma fractionalBlock_mass_identity {J : Type*} [Fintype J] {k : ℕ}
    (Q : J → (Fin k → E) × Label k → ℝ≥0∞) (hQ : ∀ j, Measurable (Q j))
    (f : J → E → ℝ≥0∞) (hf : ∀ j, Measurable (f j))
    (μ : Measure E) [SFinite μ] {S : Set E} (hS : MeasurableSet S) :
    (∫⁻ s in S, fractionalBlock Q f s ∂μ) =
      ∑ j, ∫⁻ s, capKernelValue (Q j) s ∂(μ.withDensity (f j)).restrict S := by
  have he (s : E) : fractionalBlock Q f s = ∑ j, f j s * capKernelValue (Q j) s := by
    unfold fractionalBlock capKernelValue
    rw [lintegral_finsetSum _ (fun j _ => by simp only [rowMap_apply]; fun_prop)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [lintegral_mul_const _ (by simp only [rowMap_apply]; fun_prop)]
    exact mul_comm _ _
  simp_rw [he]
  rw [lintegral_finsetSum _ (fun j _ => show Measurable (fun s => f j s * capKernelValue (Q j) s) from
    (hf j).mul (measurable_capKernelValue (hQ j)))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [restrict_withDensity hS]
  exact (lintegral_withDensity_eq_lintegral_mul _ (hf j) (measurable_capKernelValue (hQ j))).symm

theorem one_block_all_radii :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d : ℕ, 16 ≤ d →
      let k := d/4
      let β : ℝ := (d:ℝ)-1-k
      ∀ N : ℕ, ∀ f : Fin N → EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
      (∀ j, Measurable (f j)) → (∀ j s, f j s ≤ 1) →
      ∀ K : ℝ, 0 ≤ K →
      (∀ j, AllBallMass (NoiselessRegression.ambientSphereLaw.withDensity (f j)) K β) →
      ∀ Q : Fin N → (Fin k → EuclideanSpace ℝ (Fin d)) × Label k → ℝ≥0∞,
      (∀ j, Measurable (Q j)) → (∀ z, ∑ j, Q j z ≤ 1) →
      AllBallMass (NoiselessRegression.ambientSphereLaw.withDensity (fractionalBlock Q f))
        (C^d*(N:ℝ)^(1/(k:ℝ))*K) β := by
  refine ⟨16384,by norm_num,?_⟩
  intro d hd k β N f hf hf1 K hK hlocal Q hQ hQsum z R hR
  let : NeZero d := ⟨by omega⟩
  have hk : 4 ≤ k := by dsimp [k]; omega
  have hkd : k ≤ d := by dsimp [k]; omega
  have hdk : d ≤ 32*k := by dsimp [k]; omega
  have hk2 : k+2 ≤ d := by dsimp [k]; omega
  have hkn : k-1+1=k := by omega
  have hknR : ((k-1:ℕ):ℝ)+1=k := by exact_mod_cast hkn
  have hβ : β ≤ d := by dsimp [β]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have hmargin : ((k-1:ℕ):ℝ)+k ≤ β := by
    have hn : 3*k ≤ d := by dsimp [k]; omega
    have hnR : 3*(k:ℝ) ≤ d := by exact_mod_cast hn
    dsimp [β]; linarith
  let u : Fin k → EuclideanSpace ℝ (Fin d) := (EuclideanSpace.basisFun (Fin d) ℝ) ∘ Fin.castLE hkd
  have hu : Orthonormal ℝ u := (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.comp _ (Fin.castLE_injective hkd)
  let μ (j : Fin N) := sphereWeightedRestriction (f j) (Metric.closedBall z R)
  let (j : Fin N) : IsFiniteMeasure (μ j) := sphereWeightedRestriction_finite (hf1 j) _
  have hs (j : Fin N) : (μ j).support ⊆ Metric.closedBall z R := sphereWeightedRestriction_support Subset.rfl
  have hl (j : Fin N) : AllBallMass (μ j) K β := fun c r hr =>
    (Measure.restrict_le_self _).trans (hlocal j c r hr)
  have hac (j : Fin N) (A : Fin k → EuclideanSpace ℝ (Fin d)) (hA : Orthonormal ℝ A) :
      (μ j).map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ)) :=
    ((Measure.absolutelyContinuous_of_le (sphereWeightedRestriction_le (hf1 j) _)).map
      (by fun_prop)).trans (sphere_frame_ac (by simpa using hk2) hA)
  have hQ1 (j : Fin N) (x) : Q j x ≤ 1 :=
    (Finset.single_le_sum (fun i _ => bot_le) (Finset.mem_univ j)).trans (hQsum x)
  have hb' (j : Fin N) : (∫⁻ s, capKernelValue (Q j) s ∂μ j) ≤
      ENNReal.ofReal ((16384:ℝ)^d)*ENNReal.ofReal (K*R^β)*(capReference (Q j) z R)^(1-1/(k:ℝ)) := by
    have hh := localized_fractional_kernel_bound (hl j) hK z hR (hs j) (n := k-1)
      (by omega) (by omega) (by simpa using hkd) (by simpa using hdk) (by simpa using hβ)
      hmargin (hQ j) (hQ1 j) hu (hac j)
    simpa only [finrank_euclideanSpace_fin,hknR] using hh
  have hp : (1:ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hθ : 0 ≤ 1-1/(k:ℝ) := by
    have hh : 1/(k:ℝ) ≤ 1 := (div_le_one (by linarith)).mpr hp.le
    linarith
  rw [withDensity_apply _ Metric.isClosed_closedBall.measurableSet,
    fractionalBlock_mass_identity Q hQ f hf _ Metric.isClosed_closedBall.measurableSet]
  calc
    _ ≤ ∑ j, ENNReal.ofReal ((16384:ℝ)^d)*ENNReal.ofReal (K*R^β)*(capReference (Q j) z R)^(1-1/(k:ℝ)) :=
      Finset.sum_le_sum (fun j _ => hb' j)
    _ = ENNReal.ofReal ((16384:ℝ)^d)*ENNReal.ofReal (K*R^β)*
        ∑ j, (capReference (Q j) z R)^(1-1/(k:ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ ENNReal.ofReal ((16384:ℝ)^d)*ENNReal.ofReal (K*R^β)*
        ((N:ℝ≥0∞)^(1/(k:ℝ))) := by
      apply mul_le_mul' le_rfl
      apply (NoiselessRegression.finite_rpow_holder (fun j => capReference (Q j) z R) hp).trans
      have hsum := capReference_sum_le_one Q hQ hQsum z R
      simpa only [Fintype.card_fin,ENNReal.one_rpow,mul_one] using
        mul_le_mul' (le_rfl : (N:ℝ≥0∞)^(1/(k:ℝ)) ≤ _) (ENNReal.rpow_le_rpow hsum hθ)
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (16384:ℝ)^d*(N:ℝ)^(1/(k:ℝ))*K),
        ENNReal.ofReal_mul (by positivity : 0 ≤ (16384:ℝ)^d*(N:ℝ)^(1/(k:ℝ))),
        ENNReal.ofReal_mul (by positivity : 0 ≤ (16384:ℝ)^d),ENNReal.ofReal_mul hK,
        ← ENNReal.ofReal_rpow_of_nonneg (by positivity : (0:ℝ) ≤ N) (by positivity : (0:ℝ) ≤ 1/k),
        ENNReal.ofReal_natCast]
      ring

end ProjectionMoments

end

end OAI
