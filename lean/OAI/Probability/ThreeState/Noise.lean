import Mathlib
import OAI.Probability.ThreeState.PoissonCritical

namespace OAI

/-! Additional channel noise and nonnegative-channel non-reconstruction. -/

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

lemma pmf_ext_mass {α : Type*} {p q : PMF α} (he : ∀ a, mass p a=mass q a) : p=q := by
  apply PMF.ext
  intro a
  rcases (ENNReal.toReal_eq_toReal_iff (p a) (q a)).mp (he a) with he | he | he
  · exact he
  · exact False.elim ((q.apply_ne_top a) he.2)
  · exact False.elim ((p.apply_ne_top a) he.1)

lemma channelPMF_comp (a b : ℝ) (ha : Admissible a) (hb : Admissible b) (hab : Admissible (a*b)) (i : Spin) :
    (channelPMF a ha i).bind (channelPMF b hb) = channelPMF (a*b) hab i := by
  apply pmf_ext_mass
  intro j
  rw [mass_bind]
  simp only [tsum_fintype, mass_channelPMF]
  fin_cases i <;> fin_cases j <;> simp [channel, Fin.sum_univ_succ] <;> ring

noncomputable def orderedExtraNoise (r : ℝ) (hr : Admissible r) (n : ℕ)
    (y : OrderedObservation n) : PMF (OrderedObservation n) :=
  (channelPMF r hr 0).map (fun j : Spin => renameOrdered n (Equiv.addRight j) y)

lemma orderedLaw_extraNoise (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (r : ℝ) (hr : Admissible r) (n : ℕ) (i : Spin) :
    (orderedLaw offspring lam h n i).bind (orderedExtraNoise r hr n) =
      (channelPMF r hr i).bind (orderedLaw offspring lam h n) := by
  unfold orderedExtraNoise
  simp only [PMF.map, Function.comp_def]
  rw [PMF.bind_comm]
  have he (j : Spin) : (orderedLaw offspring lam h n i).bind
      (fun y => PMF.pure (renameOrdered n (Equiv.addRight j) y)) = orderedLaw offspring lam h n (i+j) := by
    exact orderedLaw_rename offspring lam h (Equiv.addRight j) n i
  simp_rw [he]
  have hm : (channelPMF r hr 0).map (Equiv.addLeft i) = channelPMF r hr i := by
    simpa using channelPMF_map r hr (Equiv.addLeft i) 0
  rw [← hm, PMF.bind_map]
  rfl

 

noncomputable def orderedDegrade (r : ℝ) (hr : Admissible r) :
    (n : ℕ) → OrderedObservation n → PMF (OrderedObservation n)
  | 0 => PMF.pure
  | n+1 => fun ⟨k,v⟩ => (vectorTraverse (fun y => (orderedDegrade r hr n y).bind (orderedExtraNoise r hr n)) k v).map (Sigma.mk k)

lemma orderedLaw_degrade (offspring : PMF ℕ) (lam r : ℝ) (h : Admissible lam)
    (hr : Admissible r) (hp : Admissible (lam*r)) (n : ℕ) (i : Spin) :
    (orderedLaw offspring lam h n i).bind (orderedDegrade r hr n) =
      orderedLaw offspring (lam*r) hp n i := by
  induction n generalizing i with
  | zero => simp only [orderedLaw, orderedDegrade, PMF.bind_pure]
  | succ n ih =>
    simp only [orderedLaw, orderedDegrade, PMF.bind_bind, PMF.bind_map, Function.comp_def]
    apply congrArg (PMF.bind offspring)
    funext k
    rw [← PMF.map_bind, iidVector_bind_traverse, PMF.bind_bind]
    have he (j : Spin) : (orderedLaw offspring lam h n j).bind
        (fun y => (orderedDegrade r hr n y).bind (orderedExtraNoise r hr n)) =
          (channelPMF r hr j).bind (orderedLaw offspring (lam*r) hp n) := by
      rw [← PMF.bind_bind, ih, orderedLaw_extraNoise]
    simp_rw [he]
    rw [← PMF.bind_bind, channelPMF_comp lam r h hr hp]

lemma orderedAdvantage_degrade (offspring : PMF ℕ) (lam r : ℝ) (h : Admissible lam)
    (hr : Admissible r) (hp : Admissible (lam*r)) (n : ℕ) :
    advantage (orderedLaw offspring (lam*r) hp n) ≤ advantage (orderedLaw offspring lam h n) := by
  have he : orderedLaw offspring (lam*r) hp n = fun i =>
      (orderedLaw offspring lam h n i).bind (orderedDegrade r hr n) := funext (fun i => (orderedLaw_degrade offspring lam r h hr hp n i).symm)
  rw [he]
  exact advantage_bind_le _ _

lemma orderedAdvantage_antitone (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) :
    Antitone (fun n => advantage (orderedLaw offspring lam h n)) := by
  apply antitone_nat_of_succ_le
  intro n
  have he : orderedLaw offspring lam h (n+1) = fun i =>
      (orderedLaw offspring lam h n i).bind (orderedGrow offspring lam h n) := funext (fun i => (orderedLaw_grow offspring lam h n i).symm)
  rw [he]
  exact advantage_bind_le _ _

lemma ordered_tendsto_zero_of_uniform_fixedpoints (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (hunif : ∀ Q : ProbabilityMeasure Message, IsPosteriorFixedPoint offspring lam h Q → SpinSymmetric Q → posteriorMu Q=0) :
    Tendsto (fun n => advantage (orderedLaw offspring lam h n)) atTop (𝓝 0) := by
  obtain ⟨Q,hQ,hs,φ,hφ,hlim⟩ := ordered_exists_symmetric_fixedpoint offspring lam h
  have htv := integral_tv_zero_of_mu_zero Q (hunif Q hQ hs)
  have hordered := advantage_tendsto_of_likelihood (fun n => orderedLaw offspring lam h (φ n)) hlim
  rw [htv] at hordered
  let a := fun n => advantage (orderedLaw offspring lam h n)
  have hb : BddBelow (Set.range a) := ⟨0, by rintro x ⟨n,rfl⟩; exact advantage_nonneg _⟩
  have hall := tendsto_atTop_ciInf (orderedAdvantage_antitone offspring lam h) hb
  have hz : (⨅ n, a n)=0 := tendsto_nhds_unique (hall.comp hφ.tendsto_atTop) hordered
  rwa [hz] at hall

end ThreeState
namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

 

theorem poisson_nonnegative_nonreconstruction (d : ℝ) (hd : 1 < d) (lam : ℝ)
    (h : Admissible lam) (hl0 : 0 ≤ lam) (hc : d*lam^2 ≤ 1) :
    Tendsto (poissonAdvantage d (by linarith) lam h) atTop (𝓝 0) := by
  have hd0 : 0 < d := by linarith
  let L := Real.sqrt d⁻¹
  have hL0 : 0 < L := Real.sqrt_pos.mpr (inv_pos.mpr hd0)
  have hLsq : L^2=d⁻¹ := Real.sq_sqrt (inv_nonneg.mpr hd0.le)
  have hK : d*L^2=1 := by rw [hLsq, mul_inv_cancel₀ hd0.ne']
  have hL1 : L≤1 := by
    have hi : d⁻¹≤1 := (inv_le_one₀ hd0).mpr hd.le
    nlinarith [sq_nonneg L]
  have hL : Admissible L := ⟨by linarith, hL1⟩
  have hlL : lam≤L := by
    have hh : lam^2≤L^2 := (mul_le_mul_iff_right₀ hd0).mp (by nlinarith only [hc,hK])
    nlinarith
  let r := lam/L
  have hr0 : 0≤r := div_nonneg hl0 hL0.le
  have hr1 : r≤1 := (div_le_one hL0).mpr hlL
  have hr : Admissible r := ⟨by linarith, hr1⟩
  have heq : L*r=lam := by dsimp [r]; field_simp
  have hp : Admissible (L*r) := by rwa [heq]
  have ht := ordered_tendsto_zero_of_uniform_fixedpoints (poissonOffspring d hd0.le) L hL
    (poisson_positive_critical_uniform d hd L hL hL0 hK)
  apply squeeze_zero (fun n => advantage_nonneg _)
    (g := fun n => advantage (orderedLaw (poissonOffspring d hd0.le) L hL n)) _ ht
  intro n
  have hg := orderedAdvantage_degrade (poissonOffspring d hd0.le) L r hL hr hp n
  have heLaw : orderedLaw (poissonOffspring d hd0.le) (L*r) hp n = orderedLaw (poissonOffspring d hd0.le) lam h n := by
    congr 1
  rw [heLaw] at hg
  exact (orderedAdvantage_dominates (poissonOffspring d hd0.le) lam h n).trans hg

end ThreeState

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

 
theorem regular_nonnegative_nonreconstruction (b : ℕ) (hb : 2 ≤ b) (lam : ℝ)
    (h : Admissible lam) (hl0 : 0 ≤ lam) (hc : (b:ℝ)*lam^2 ≤ 1) :
    Tendsto (regularAdvantage b lam h) atTop (𝓝 0) := by
  have hb0 : (0:ℝ) < b := by exact_mod_cast (show 0<b by omega)
  let L := Real.sqrt ((b:ℝ)⁻¹)
  have hL0 : 0 < L := Real.sqrt_pos.mpr (inv_pos.mpr hb0)
  have hLsq : L^2=(b:ℝ)⁻¹ := Real.sq_sqrt (inv_nonneg.mpr hb0.le)
  have hK : (b:ℝ)*L^2=1 := by rw [hLsq, mul_inv_cancel₀ hb0.ne']
  have hbr : (2:ℝ)≤b := by exact_mod_cast hb
  have hL1 : L≤1 := by nlinarith [sq_nonneg L]
  have hL : Admissible L := ⟨by linarith, hL1⟩
  have hlL : lam≤L := by
    have hh : lam^2≤L^2 := (mul_le_mul_iff_right₀ hb0).mp (by nlinarith only [hc,hK])
    nlinarith
  let r := lam/L
  have hr0 : 0≤r := div_nonneg hl0 hL0.le
  have hr1 : r≤1 := (div_le_one hL0).mpr hlL
  have hr : Admissible r := ⟨by linarith, hr1⟩
  have heq : L*r=lam := by dsimp [r]; field_simp
  have hp : Admissible (L*r) := by rwa [heq]
  have ht := ordered_tendsto_zero_of_uniform_fixedpoints (PMF.pure b) L hL
    (regular_positive_critical_uniform b hb L hL hL0 hK)
  apply squeeze_zero (fun n => advantage_nonneg _)
    (g := fun n => advantage (orderedLaw (PMF.pure b) L hL n)) _ ht
  intro n
  have hg := orderedAdvantage_degrade (PMF.pure b) L r hL hr hp n
  have heLaw : orderedLaw (PMF.pure b) (L*r) hp n = orderedLaw (PMF.pure b) lam h n := by
    congr 1
  rw [heLaw] at hg
  exact (orderedAdvantage_dominates (PMF.pure b) lam h n).trans hg

end ThreeState

end OAI
