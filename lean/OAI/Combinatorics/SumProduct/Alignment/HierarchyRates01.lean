import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.IntegerArrays15
import OAI.Combinatorics.SumProduct.Alignment.PivotExtension02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
open scoped BigOperators BoundedContinuousFunction Topology NNReal ENNReal
end

 

 

 

noncomputable section
open Filter
open scoped Topology
namespace SourceHierarchyRates
open MicrocellScale AdmissibleMicrocellBoundary

 

lemma source_modulus_size (M W w : ℕ) (hM : 0 < M) (hW : 0 < W)
    (hdiv : W^w ∣ M) :
    0 < (M : ℤ)*(W : ℤ)^w ∧ ((M : ℤ)*(W : ℤ)^w : ℝ) ≤ (M : ℝ)^2 := by
  have hp : 0 < W^w := pow_pos hW _
  have hb : W^w ≤ M := Nat.le_of_dvd hM hdiv
  constructor
  · exact mul_pos (by exact_mod_cast hM) (by positivity)
  · have hbr : (W : ℝ)^w ≤ M := by exact_mod_cast hb
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) M]

variable {M P H X W : ℕ → ℕ}

lemma earlier_dominates_modulus (hM : ∀ N, 0 < M N)
    (hd : Dominates (fun N => (H N : ℝ)) (earlierScale M P)) (k : ℕ) (hk : 0 < k) :
    Tendsto (fun N => (M N : ℝ)^k/(H N : ℝ)) atTop (𝓝 0) := by
  have hh : Tendsto (fun N => (earlierScale M P N)^k/(H N : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, inv_div, Real.rpow_natCast] using
      tendsto_inv_atTop_zero.comp (hd (k : ℝ) (by exact_mod_cast hk))
  apply squeeze_zero (fun N => by positivity) (fun N => ?_) hh
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply pow_le_pow_left₀ (by exact_mod_cast (hM N).le)
  unfold earlierScale
  linarith [Nat.cast_nonneg (α := ℝ) (P N)]

lemma eventually_height_ge_modulus_sq
    (hd : Dominates (fun N => (H N : ℝ)) (earlierScale M P)) :
    ∀ᶠ N in atTop, (M N : ℝ)^2 ≤ H N := by
  filter_upwards [(hd 2 (by norm_num)).eventually_ge_atTop 1] with N hn
  rw [Real.rpow_two] at hn
  have hs : 0 < earlierScale M P N := by
    unfold earlierScale
    positivity
  have hm : (M N : ℝ) ≤ earlierScale M P N := by
    unfold earlierScale
    linarith [Nat.cast_nonneg (α := ℝ) (P N)]
  have hh := (le_div_iff₀ (sq_pos_of_pos hs)).mp hn
  nlinarith [Nat.cast_nonneg (α := ℝ) (M N)]

 

lemma eventually_interval_four_modulus (hM : ∀ N, 0 < M N)
    (hH : ∀ N, 0 < H N) (hX : ∀ N, 0 < X N)
    (hWM : ∀ N, W N ≤ M N)
    (hd : Dominates (fun N => (H N : ℝ)) (earlierScale M P))
    (hx : Dominates (fun N => Real.log (X N : ℝ)) (fun N => (H N : ℝ))) :
    ∀ᶠ N in atTop, 4*W N ≤ X N := by
  have hl : Tendsto (fun N => Real.log (X N : ℝ)/(H N : ℝ)) atTop atTop := by
    simpa only [Real.rpow_one] using hx 1 zero_lt_one
  filter_upwards [eventually_height_ge_modulus_sq hd, hl.eventually_ge_atTop 4] with N hMN hn
  have hm : (1 : ℝ) ≤ M N := by exact_mod_cast hM N
  have hh : (0 : ℝ) < H N := by exact_mod_cast hH N
  have hw : (W N : ℝ) ≤ M N := by exact_mod_cast hWM N
  have hlog : Real.log (X N : ℝ) ≤ X N := Real.log_le_self (by exact_mod_cast (hX N).le)
  have hi := (le_div_iff₀ hh).mp hn
  have hhX : (4 : ℝ)*W N ≤ X N := by nlinarith
  exact_mod_cast hhX

lemma raw_interval_tendsto (hH : ∀ N, 0 < H N) (hX : ∀ N, 0 < X N)
    (hx : Dominates (fun N => Real.log (X N : ℝ)) (fun N => (H N : ℝ))) :
    Tendsto X atTop atTop := by
  have hl : Tendsto (fun N => Real.log (X N : ℝ)/(H N : ℝ)) atTop atTop := by
    simpa only [Real.rpow_one] using hx 1 zero_lt_one
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  apply tendsto_atTop_mono' atTop _ hl
  apply Eventually.of_forall
  intro N
  have hh : (1 : ℝ) ≤ H N := by exact_mod_cast hH N
  calc
    Real.log (X N : ℝ)/(H N : ℝ) ≤ (X N : ℝ)/(H N : ℝ) :=
      div_le_div_of_nonneg_right (Real.log_le_self (by exact_mod_cast (hX N).le)) (by positivity)
    _ ≤ X N := div_le_self (by positivity) hh

lemma raw_over_modulus_tendsto (hH : ∀ N, 0 < H N) (hX : ∀ N, 0 < X N)
    (L : ℕ → ℤ) (hL : ∀ N, 0 < L N) (hLM : ∀ N, (L N : ℝ) ≤ (M N : ℝ)^2)
    (hd : Dominates (fun N => (H N : ℝ)) (earlierScale M P))
    (hx : Dominates (fun N => Real.log (X N : ℝ)) (fun N => (H N : ℝ))) :
    Tendsto (fun N => (X N : ℝ)/(L N : ℝ)) atTop atTop := by
  have hl : Tendsto (fun N => Real.log (X N : ℝ)/(H N : ℝ)) atTop atTop := by
    simpa only [Real.rpow_one] using hx 1 zero_lt_one
  apply tendsto_atTop_mono' atTop _ hl
  filter_upwards [eventually_height_ge_modulus_sq hd] with N hMH
  calc
    Real.log (X N : ℝ)/(H N : ℝ) ≤ (X N : ℝ)/(H N : ℝ) :=
      div_le_div_of_nonneg_right (Real.log_le_self (by exact_mod_cast (hX N).le))
        (by exact_mod_cast (hH N).le)
    _ ≤ (X N : ℝ)/(L N : ℝ) := div_le_div_of_nonneg_left (by positivity)
      (by exact_mod_cast hL N) ((hLM N).trans hMH)

 

theorem source_translation_error (hM : ∀ N, 0 < M N)
    (hH : ∀ N, 0 < H N) (hX : ∀ N, 0 < X N) (hWM : ∀ N, W N ≤ M N)
    (L : ℕ → ℤ) (hL : ∀ N, 0 ≤ L N) (hLM : ∀ N, (L N : ℝ) ≤ (M N : ℝ)^2)
    (hd : Dominates (fun N => (H N : ℝ)) (earlierScale M P))
    (hx : Dominates (fun N => Real.log (X N : ℝ)) (fun N => (H N : ℝ))) (K : ℝ) :
    Tendsto (fun N => 4*(W N : ℝ)*K*(L N : ℝ)/(X N : ℝ)) atTop (𝓝 0) := by
  have hl : Tendsto (fun N => Real.log (X N : ℝ)/(H N : ℝ)) atTop atTop := by
    simpa only [Real.rpow_one] using hx 1 zero_lt_one
  have hHX : ∀ᶠ N in atTop, (H N : ℝ) ≤ X N := by
    filter_upwards [hl.eventually_ge_atTop 1] with N hn
    have hh : (0 : ℝ) < H N := by exact_mod_cast hH N
    have he := (le_div_iff₀ hh).mp hn
    have hlog := Real.log_le_self (show (0 : ℝ) ≤ X N by exact_mod_cast (hX N).le)
    linarith
  have hb : Tendsto (fun N => (W N : ℝ)*(L N : ℝ)/(X N : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun N =>
      div_nonneg (mul_nonneg (by positivity) (by exact_mod_cast hL N)) (by positivity))) ?_
        (earlier_dominates_modulus hM hd 3 (by norm_num))
    filter_upwards [hHX] with N hn
    have hm : (0 : ℝ) ≤ M N := by positivity
    have hw : (W N : ℝ) ≤ M N := by exact_mod_cast hWM N
    have hLn : (0 : ℝ) ≤ L N := by exact_mod_cast hL N
    have hbound : (W N : ℝ)*(L N : ℝ) ≤ (M N : ℝ)^3 := by
      calc
        _ ≤ (M N : ℝ)*(M N : ℝ)^2 := mul_le_mul hw (hLM N) hLn hm
        _ = _ := by ring
    calc
      _ ≤ (M N : ℝ)^3/(X N : ℝ) := div_le_div_of_nonneg_right hbound (by positivity)
      _ ≤ (M N : ℝ)^3/(H N : ℝ) := div_le_div_of_nonneg_left (by positivity)
        (by exact_mod_cast hH N) hn
  convert hb.const_mul (4*K) using 1 <;> try simp
  funext N
  ring

end SourceHierarchyRates
end

 

 

 

noncomputable section
open scoped BigOperators BoundedContinuousFunction Topology NNReal ENNReal
namespace SourceIntegerArrays.GlobalJoint.SourceFrozenFamily
open ProductExposureLabels ProductExposureLaw SourceExposureSlots SourceResidueAlignment
open ConstructedWordPlan.GlobalWordPlan ConstructedWordPlan.AlignmentScales
open ConstructedWordPlan.RationalPivotPlan
open ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic
open RawHarmonicProbability
attribute [local instance] Classical.propDecidable
variable {a : ℕ} (D : Pivot a)

variable (s r : ℕ) (hs : 1 ≤ s) (Fs : Finset (Scale a)) (q₀ : ℕ) (b₀ : Scale a)
local notation "I" => FiniteModelSlots.Index D s r hs Fs q₀ b₀

open Filter MeasureTheory RationalLattice MalcevCharacters
open MicrocellScale AdmissibleMicrocellBoundary RoughScales IntegerAlignment
open RoughSamplingWeights SourceMacroSelection

section Harmonic
variable (G₀ : Fin D.targets → ℚ → Fin r → Type)
variable [∀ t v c, Group (G₀ t v c)] [∀ t v c, TopologicalSpace (G₀ t v c)]
variable [∀ t v c, IsTopologicalGroup (G₀ t v c)]
variable (Γ₀ : ∀ t v c, Subgroup (G₀ t v c))
variable (n₀ : Fin D.targets → ℚ → Fin r → ℕ)
variable (c₀ : ∀ t v c, RealCoordinates (G₀ t v c) (n₀ t v c))
variable (hsk : ∀ t v c, SecondKind (c₀ t v c))
variable (A₀ : ∀ t v c, CubeFaces.Filtration (G₀ t v c))
variable (weight : ∀ t v c, Fin (n₀ t v c) → ℕ)
variable (hA : ∀ t v c k (g : G₀ t v c), g ∈ (A₀ t v c).level k ↔
  ∀ j, weight t v c j < k → (c₀ t v c).coord g j = 0)
variable (hw : ∀ t v c j, 0 < weight t v c j)
include hsk hA hw

theorem source_uniform_extension
    (hΓ : ∀ t v c g, g ∈ Γ₀ t v c ↔ ∀ j, ∃ z : ℤ, (c₀ t v c).coord g j = z)
    (hmono : ∀ t v c, Monotone (weight t v c))
    (h0 : ∀ t v c, (A₀ t v c).level 0 = ⊤)
    (h1 : ∀ t v c, (A₀ t v c).level 1 = ⊤)
    (hstep : ∀ t v c, (A₀ t v c).level (s+1) = ⊥)
    (M J R H : ℕ → ℕ) (L : ℕ → ℤ) (ht : ℕ → Fin a → ℤ)
    (g₀ x₀ : ∀ t, ℕ → (Fin (h D t) → ℕ) → ∀ v c, ℤ → ℤ → G₀ t v c)
    (obs₀ : ∀ t, ℕ → (Fin (h D t) → ℕ) → ∀ v c, ℤ → ℤ → ((G₀ t v c) ⧸ Γ₀ t v c) →ᵇ ℝ)
    (w0 Xp : ℕ → ℕ) (X : ℕ → Fin a → ℕ)
    (hw0 : Tendsto w0 atTop atTop)
    (hX : ∀ N j, 4*primorial (w0 N) ≤ X N j)
    (hXp : ∀ N, 4*primorial (w0 N) ≤ Xp N)
    (hXt : ∀ j, Tendsto (fun N => X N j) atTop atTop)
    (hXpt : Tendsto Xp atTop atTop)
    (hWM : ∀ N, (primorial (w0 N) : ℤ) ∣ (M N : ℤ))
    (hM : ∀ N, 0 < M N) (hMs : ∀ N, RoughScales.Smooth (w0 N) (M N : ℤ))
    (hJ : ∀ N, 0 < J N) (hRJ : ∀ N, R N = M N*J N)
    (hL : ∀ N, 0 < L N) (hsm : ∀ N, RoughScales.Smooth (w0 N) (L N))
    (hWL : ∀ N, (primorial (w0 N) : ℤ) ∣ L N) (hML : ∀ N, (M N : ℤ) ∣ L N)
    (hLexact : ∀ N, L N = (M N : ℤ)*(primorial (w0 N) : ℤ)^(w0 N))
    (hXL : ∀ t (j : Fin (m D t)), Tendsto (fun N =>
      (X N (perm D t (j.castAdd (h D t))) : ℝ)/(L N : ℝ)) atTop atTop)
    (hH : ∀ N, 0 < H N) (hRrad : ∀ N, R N = radius (M N) (H N))
    (hdom : Dominates (fun N => (H N : ℝ)) (earlierScale M (fun N => previousProduct D (X N))))
    (hxdom : Dominates (fun N => Real.log (Xp N : ℝ)) (fun N => (H N : ℝ)))
    (hpowWM : ∀ N, primorial (w0 N)^(w0 N) ∣ M N)
    (hq₀ : 0 < q₀) (hht : ∀ N j, 0 < ht N j)
    (hheight : ∀ N e, height (ht N) (D.added e) ≤ M N)
    (hd : ∀ e, Disjoint (D.added e) (D.tail (D.owner e)))
    (hQq : terminalDenom D s r hs Fs b₀ ∣ q₀)
    (hb₀ : ∀ j, 0 < b₀ j) (hFs : ∀ b ∈ Fs, ∀ j, 0 < b j)
    (hratio : ∀ N e, ∃ d : ℤ, height (ht N) (D.added e) =
      height (ht N) (block D.index D.tail (D.owner e)) * ((primorial (w0 N) : ℤ)^(w0 N) * d))
    (metric : ∀ t v c, MetricSpace ((G₀ t v c) ⧸ Γ₀ t v c))
    (hmetric : ∀ t v c, QuotientGroup.instTopologicalSpace (Γ₀ t v c) =
      (metric t v c).toUniformSpace.toTopologicalSpace) :
    letI : ∀ t v c, MetricSpace ((G₀ t v c) ⧸ Γ₀ t v c) :=
      fun t v c => (metric t v c).replaceTopology (hmetric t v c)
    ∀ (Kobs : ℝ≥0) (Bobs : ℝ),
      (∀ t N y v c b r', LipschitzWith Kobs (obs₀ t N y v c b r')) →
      (∀ t N y v c b r' z, |obs₀ t N y v c b r' z| ≤ Bobs) →
      ∀ (Bs : Finset (Scale a)), b₀ ∈ Bs →
      pivotModulus s r hs D Fs Bs ∣ q₀ → ∀ (τ : ℝ), 0 < τ →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ E : Set (Fin a → ℕ),
    let μ := jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _) (hX N) (hXp N)
    (((pivotOptions s r hs D Fs).card : ℝ)⁻¹/3)*μ.real {z | z.1 ∈ E} ≤
      (slotCount D s r hs Fs q₀ b₀ : ℝ)*μ.real {z | z.1 ∈ E ∧
        pivotProperty D s r hs Fs b₀ G₀ Γ₀ M H g₀ x₀ obs₀ ht N z.1 z.2 τ} + ε := by
  let : ∀ t v c, MetricSpace ((G₀ t v c) ⧸ Γ₀ t v c) :=
    fun t v c => (metric t v c).replaceTopology (hmetric t v c)
  intro Kobs Bobs hLip hBound Bs hb hq τ hτ ε hε
  let c : ℝ := ((pivotOptions s r hs D Fs).card : ℝ)⁻¹/3
  let V : ℝ := slotCount D s r hs Fs q₀ b₀
  let μ := fun N => jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _) (hX N) (hXp N)
  let d := family D s r hs Fs q₀ b₀ G₀ Γ₀ M J R H L (heightCoeff D q₀ ht) g₀ x₀ obs₀
  let bad := fun N => {z | cellRatio (Xp N) (primorial (w0 N)) (M N) (J N) z.2
    (primorial_pos _) (hXp N) {k | ((d.atTime N).localModel z).modelSuccess (coord D)
      (k : ℤ) s r hs (FiniteModelSlots.formula D s r hs Fs q₀ b₀) Fs q₀ b₀ τ} ≤ c}
  let err := fun N => 4*(primorial (w0 N) : ℝ)*(slotBudget D s r hs Fs q₀ b₀ : ℝ)*(L N : ℝ)/(Xp N : ℝ)
  have hLsize : ∀ N, (L N : ℝ) ≤ (M N : ℝ)^2 := by
    intro N
    rw [hLexact N]
    simpa only [Int.cast_mul, Int.cast_pow] using (SourceHierarchyRates.source_modulus_size (M N) (primorial (w0 N)) (w0 N)
      (hM N) (primorial_pos _) (hpowWM N)).2
  have hbad : Tendsto (fun N => μ N (bad N)) atTop (𝓝 0) :=
    source_actual_harmonic D s r hs Fs q₀ b₀ G₀ Γ₀ n₀ c₀ hsk A₀ weight hA hw
      hΓ hmono h0 h1 hstep M J R H L ht g₀ x₀ obs₀ w0 Xp X hw0 hX hXp hXt hXpt
      hWM hM hMs hJ hRJ hL hsm hWL hML hLexact hXL hH hRrad hdom hxdom
      (Eventually.of_forall hLsize) hq₀ hht hheight hd metric hmetric
      Kobs Bobs hLip hBound Bs hb hq τ hτ
  have hbadR : Tendsto (fun N => (μ N).real (bad N)) atTop (𝓝 0) := by
    simpa only [measureReal_def, ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hbad
  have hp : ∀ N, 0 < Xp N := by
    intro N
    have := hXp N
    have := primorial_pos (w0 N)
    omega
  have hWMle : ∀ N, primorial (w0 N) ≤ M N := by
    intro N
    exact Nat.le_of_dvd (hM N) (Int.natCast_dvd_natCast.mp (hWM N))
  have herr : Tendsto err atTop (𝓝 0) :=
    SourceHierarchyRates.source_translation_error hM hH hp hWMle L
      (fun N => (hL N).le) hLsize hdom hxdom (slotBudget D s r hs Fs q₀ b₀ : ℝ)
  have htotal : Tendsto (fun N => c*(μ N).real (bad N)+V*err N) atTop (𝓝 0) := by
    simpa using (hbadR.const_mul c).add (herr.const_mul V)
  have hXLp : Tendsto (fun N => (Xp N : ℝ)/(L N : ℝ)) atTop atTop :=
    SourceHierarchyRates.raw_over_modulus_tendsto hH hp L hL hLsize hdom hxdom
  have hlarge : ∀ᶠ N in atTop,
      slotBudget D s r hs Fs q₀ b₀*L N < (Xp N : ℤ) := by
    filter_upwards [hXLp.eventually_gt_atTop (slotBudget D s r hs Fs q₀ b₀ : ℝ)] with N hN
    have hl : (0 : ℝ) < L N := by exact_mod_cast hL N
    have hh := (lt_div_iff₀ hl).mp hN
    exact_mod_cast hh
  filter_upwards [htotal.eventually_lt_const hε, hlarge,
    hw0.eventually_ge_atTop (q₀+1)] with N hN hlargeN hwN
  intro E
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have he := source_actual_extension D s r hs Fs q₀ b₀ G₀ Γ₀ M J R H L
    g₀ x₀ obs₀ ht N (w0 N) (X N) (Xp N) (primorial_pos _) (hX N) (hXp N)
    (hM N) (hJ N) hq₀ hQq hwN (hL N) (hsm N) (hWL N) (hML N)
    hd hb₀ hFs (hht N) (hratio N) hlargeN τ c hc E
  change c*((μ N).real {z | z.1 ∈ E}-(μ N).real (bad N)) ≤
    V*((μ N).real {z | z.1 ∈ E ∧ pivotProperty D s r hs Fs b₀ G₀ Γ₀ M H
      g₀ x₀ obs₀ ht N z.1 z.2 τ}+err N) at he
  change c*(μ N).real {z | z.1 ∈ E} ≤ V*(μ N).real {z | z.1 ∈ E ∧
    pivotProperty D s r hs Fs b₀ G₀ Γ₀ M H g₀ x₀ obs₀ ht N z.1 z.2 τ}+ε
  nlinarith

end Harmonic
end SourceIntegerArrays.GlobalJoint.SourceFrozenFamily

end
end

end OAI
