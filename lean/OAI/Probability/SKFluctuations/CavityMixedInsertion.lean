import Mathlib
import OAI.Probability.SKFluctuations.ReplicaMixedInsertion

namespace OAI

/-! Cavity Mixed Insertion. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy GaussianCalculus
open scoped Topology NNReal BigOperators

 

def cutLowError (n U : ℕ) (b h K : ℕ → ℝ) (j : ℕ) : FullCoordinate n → ℝ :=
  if j < U then rowInterpolationSlope n (b j) (h j) (K j) else 0

theorem cutFullVariance_biaffine (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (l t : ℝ) (b h K : ℕ → ℝ) :
    cutFullVariance n q U l t b h K = fun j i =>
      cutFullVariance n q U 0 0 b h K j i+t*cutTSlope n U 0 b h K j i+
        l*(cutLSlope n U 0 b h K j i+t*cutLowError n U b h K j i) := by
  funext j i
  rcases i with (i | i) | (i | i) <;>
    simp only [cutFullVariance,cutTSlope,cutLSlope,cutLowError,fullVariance,
      rowInterpolationSlope,relocatedClock,Sum.elim_inl,Sum.elim_inr] <;>
    split_ifs <;> simp_all <;> ring

 

theorem mixed_cutDisorderExpect (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) {l t : ℝ} (hl : l ∈ Ioo (0:ℝ) 1) (ht : t ∈ Ioo (0:ℝ) 1)
    (b h K : ℕ → ℝ) (hq0 : ∀ j i, 0 ≤ q j i) (hq : ∀ i, Monotone (fun j => q j i))
    (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ) (k : ℕ) :
    HasDerivAt (fun s => iteratedDeriv k (fun u => T.disorderExpect (fullWeight n)
      (fullFeature n) 0 (cutFullVariance n q U u s b h K) P x) l)
      ((ClockPolynomial.finiteMixedJet (T.testExpr P) (fullFeature n)
        (cutLSlope n U 0 b h K) (cutTSlope n U 0 b h K) (cutLowError n U b h K) l k).finiteEval
        (fullWeight n) (fullFeature n) t 0 (cutFullVariance n q U l t b h K) x) t := by
  have hp : ∀ u ∈ Ioo (0:ℝ) 1, ∀ s ∈ Ioo (0:ℝ) 1, ∀ i,
      Monotone (fun j => cutFullVariance n q U 0 0 b h K j i+s*cutTSlope n U 0 b h K j i+
        u*(cutLSlope n U 0 b h K j i+s*cutLowError n U b h K j i)) := by
    intro u hu s hs i
    have hm := cutFullVariance_monotone n q U ⟨hu.1.le,hu.2.le⟩ ⟨hs.1.le,hs.2.le⟩
      hq hb hh hK hbm hhm hKm i
    rwa [cutFullVariance_biaffine] at hm
  have hr : ∀ u ∈ Ioo (0:ℝ) 1, ∀ s ∈ Ioo (0:ℝ) 1, ∀ i,
      (0 : FullCoordinate n → ℝ) i ≤ cutFullVariance n q U 0 0 b h K 0 i+
        s*cutTSlope n U 0 b h K 0 i+
          u*(cutLSlope n U 0 b h K 0 i+s*cutLowError n U b h K 0 i) := by
    intro u hu s hs i
    have hn := cutFullVariance_nonneg n q U ⟨hu.1.le,hu.2.le⟩ ⟨hs.1.le,hs.2.le⟩ hq0 hb hh hK 0 i
    rw [cutFullVariance_biaffine] at hn
    exact hn
  have hd := T.mixed_finiteDisorderExpect (fullWeight_pos n) (fullFeature n) ho 0
    (cutFullVariance n q U 0 0 b h K) (cutLSlope n U 0 b h K) (cutTSlope n U 0 b h K)
    (cutLowError n U b h K) hp hr hl ht P x k
  have he (u s : ℝ) : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U u s b h K) P x = T.disorderExpect (fullWeight n) (fullFeature n) 0
        (fun j i => cutFullVariance n q U 0 0 b h K j i+s*cutTSlope n U 0 b h K j i+
          u*(cutLSlope n U 0 b h K j i+s*cutLowError n U b h K j i)) P x := by
    rw [cutFullVariance_biaffine]
  simp only [he]
  rw [cutFullVariance_biaffine n q U l t b h K]
  exact hd

end SKFluctuations.Cavity

 

namespace SKFluctuations.Cavity
open MeasureTheory Filter Set
open scoped Topology

 

theorem third_low_remainder (f₀ f₁ f₂ f₃ : ℝ → ℝ)
    (h₀ : Continuous f₀) (h₁ : Continuous f₁) (h₂ : Continuous f₂) (h₃ : Continuous f₃)
    (hd₀ : ∀ l ∈ Ioo (0:ℝ) 1, HasDerivAt f₀ (f₁ l) l)
    (hd₁ : ∀ l ∈ Ioo (0:ℝ) 1, HasDerivAt f₁ (f₂ l) l)
    (hd₂ : ∀ l ∈ Ioo (0:ℝ) 1, HasDerivAt f₂ (f₃ l) l) :
    f₀ 1 = f₀ 0+f₁ 0+(1/2:ℝ)*f₂ 0+
      (1/2:ℝ)*∫ l in (0:ℝ)..1, (1-l)^2*f₃ l := by
  let F := fun l => f₀ l+(1-l)*f₁ l+((1-l)^2/2)*f₂ l
  have hc : Continuous F := by unfold F; fun_prop
  have hd (l : ℝ) (hl : l ∈ Ioo (0:ℝ) 1) :
      HasDerivAt F ((1/2:ℝ)*((1-l)^2*f₃ l)) l := by
    have hs : HasDerivAt (fun x : ℝ => 1-x) (-1) l := by
      convert (hasDerivAt_id l).const_sub 1 using 1; rfl
    convert ((hd₀ l hl).add (hs.mul (hd₁ l hl))).add
      (((hs.pow 2).div_const 2).mul (hd₂ l hl)) using 1; try rfl
    simp only [Pi.pow_apply]
    ring
  have hi : IntervalIntegrable (fun l : ℝ => (1/2:ℝ)*((1-l)^2*f₃ l)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ) ≤ 1)
    hc.continuousOn hd hi
  rw [intervalIntegral.integral_const_mul] at H
  dsimp [F] at H
  norm_num at H
  linarith

 
theorem mixed_jet_integral (f : ℝ → ℝ) (h : ℝ → ℝ) (hf : Continuous f) (hh : Continuous h)
    (hd : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt f (h t) t) (hzero : f 0 = 0) :
    f 1 = ∫ t in (0:ℝ)..1, h t := by
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ) ≤ 1)
    hf.continuousOn hd (hh.intervalIntegrable 0 1)
  simpa only [hzero,sub_zero] using H.symm

 
theorem third_low_mixed_remainder (f₀ f₁ f₂ : ℝ → ℝ) (f₃ h : ℝ → ℝ → ℝ)
    (h₀ : Continuous f₀) (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (h₃ : Continuous (fun l => f₃ l 1))
    (ht₃ : ∀ l ∈ Icc (0:ℝ) 1, Continuous (f₃ l))
    (hth : ∀ l ∈ Icc (0:ℝ) 1, Continuous (h l))
    (hd₀ : ∀ l ∈ Ioo (0:ℝ) 1, HasDerivAt f₀ (f₁ l) l)
    (hd₁ : ∀ l ∈ Ioo (0:ℝ) 1, HasDerivAt f₁ (f₂ l) l)
    (hd₂ : ∀ l ∈ Ioo (0:ℝ) 1, HasDerivAt f₂ (f₃ l 1) l)
    (hdt : ∀ l ∈ Icc (0:ℝ) 1, ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt (f₃ l) (h l t) t)
    (hzero : ∀ l ∈ Icc (0:ℝ) 1, f₃ l 0 = 0) :
    f₀ 1 = f₀ 0+f₁ 0+(1/2:ℝ)*f₂ 0+
      (1/2:ℝ)*∫ l in (0:ℝ)..1, (1-l)^2*∫ t in (0:ℝ)..1, h l t := by
  have he (l : ℝ) (hl : l ∈ Icc (0:ℝ) 1) :=
    mixed_jet_integral (f₃ l) (h l) (ht₃ l hl) (hth l hl) (hdt l hl) (hzero l hl)
  rw [third_low_remainder f₀ f₁ f₂ (fun l => f₃ l 1) h₀ h₁ h₂ h₃ hd₀ hd₁ hd₂]
  congr 2
  apply intervalIntegral.integral_congr
  intro l hl
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hl
  dsimp only
  rw [he l hl]

 
def thirdProductJet (g f : Fin 4 → ℝ) : ℝ :=
  g 0*f 3+3*g 1*f 2+3*g 2*f 1+g 3*f 0

 

theorem thirdProductJet_hasDerivAt (g : Fin 4 → ℝ) (f : Fin 4 → ℝ → ℝ)
    (h : Fin 4 → ℝ) {t : ℝ} (hd : ∀ i, HasDerivAt (f i) (h i) t) :
    HasDerivAt (fun s => thirdProductJet g (fun i => f i s)) (thirdProductJet g h) t := by
  exact (((hd 3).const_mul (g 0)).add ((hd 2).const_mul (3*g 1))).add
    ((hd 1).const_mul (3*g 2)) |>.add ((hd 0).const_mul (g 3))

end SKFluctuations.Cavity

 

namespace SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy GaussianCalculus
open scoped Topology NNReal BigOperators

 
def cutLowJet (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ)
    (b h K : ℕ → ℝ) {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as)
    (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ) (k : ℕ) (l t : ℝ) : ℝ :=
  (ClockPolynomial.finiteLowJet (T.testExpr P) (fullFeature n)
    (cutLSlope n U 0 b h K) (cutLowError n U b h K) k).finiteEval
      (fullWeight n) (fullFeature n) t 0 (cutFullVariance n q U l t b h K) x

 
def cutMixedJet (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ)
    (b h K : ℕ → ℝ) {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as)
    (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ) (k : ℕ) (l t : ℝ) : ℝ :=
  (ClockPolynomial.finiteMixedJet (T.testExpr P) (fullFeature n)
    (cutLSlope n U 0 b h K) (cutTSlope n U 0 b h K) (cutLowError n U b h K) l k).finiteEval
      (fullWeight n) (fullFeature n) t 0 (cutFullVariance n q U l t b h K) x

theorem cutFullVariance_continuous_l (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (b h K : ℕ → ℝ) (t : ℝ) (j : ℕ) :
    Continuous (fun l => cutFullVariance n q U l t b h K j) := by
  simp only [cutFullVariance_l_affine]
  fun_prop

theorem cutFullVariance_continuous_t (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (b h K : ℕ → ℝ) (l : ℝ) (j : ℕ) :
    Continuous (fun t => cutFullVariance n q U l t b h K j) := by
  simp only [cutFullVariance_t_affine]
  fun_prop

theorem cutLowJet_continuous_l (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ)
    (b h K : ℕ → ℝ) {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as)
    (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ) (k : ℕ) (t : ℝ) :
    Continuous (fun l => cutLowJet n q U b h K T P x k l t) := by
  exact ClockPolynomial.finiteEval_continuous (fullWeight_pos n) (fullFeature n) _
    (fun _ => t) continuous_const 0 _ (cutFullVariance_continuous_l n q U b h K t)
    (fun _ => x) continuous_const

theorem cutLowJet_continuous_t (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ)
    (b h K : ℕ → ℝ) {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as)
    (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ) (k : ℕ) (l : ℝ) :
    Continuous (cutLowJet n q U b h K T P x k l) := by
  exact ClockPolynomial.finiteEval_continuous (fullWeight_pos n) (fullFeature n) _
    id continuous_id 0 _ (cutFullVariance_continuous_t n q U b h K l)
    (fun _ => x) continuous_const

theorem cutMixedJet_continuous_t (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ)
    (b h K : ℕ → ℝ) {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as)
    (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ) (k : ℕ) (l : ℝ) :
    Continuous (cutMixedJet n q U b h K T P x k l) := by
  exact ClockPolynomial.finiteEval_continuous (fullWeight_pos n) (fullFeature n) _
    id continuous_id 0 _ (cutFullVariance_continuous_t n q U b h K l)
    (fun _ => x) continuous_const

theorem cutLowJet_zero (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ)
    (b h K : ℕ → ℝ) {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as)
    (ho : MassOrdered 0 as) (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ) (l t : ℝ) :
    cutLowJet n q U b h K T P x 0 l t =
      T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K) P x := by
  unfold cutLowJet ClockPolynomial.finiteLowJet ClockPolynomial.finiteEval
  simp only [ClockPolynomial.lowJet,ClockPolynomial.rootEval,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,Polynomial.eval_one,one_mul,add_zero]
  rw [ClockTree.rootEval_testExpr (fullWeight_pos n)
    (reindexFeature (finiteJetEquiv (FullCoordinate n)) (fullFeature n)) T ho
    (fun i => (0 : FullCoordinate n → ℝ) (finiteJetEquiv _ i))
    (fun j i => cutFullVariance n q U l t b h K j (finiteJetEquiv _ i)) P
    ((coordinateEquiv (finiteJetEquiv (FullCoordinate n))).symm x)]
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    T.disorderExpect_reindex (finiteJetEquiv (FullCoordinate n)) (fullWeight n) (fullFeature n)
      0 (cutFullVariance n q U l t b h K) P ((coordinateEquiv (finiteJetEquiv _)).symm x)

theorem cutLowJet_hasDerivAt_l (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) {l t : ℝ} (hl : l ∈ Ioo (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1)
    (b h K : ℕ → ℝ) (hq0 : ∀ j i, 0 ≤ q j i) (hq : ∀ i, Monotone (fun j => q j i))
    (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ) (k : ℕ) :
    HasDerivAt (fun s => cutLowJet n q U b h K T P x k s t)
      (cutLowJet n q U b h K T P x (k+1) l t) l := by
  have hp : ∀ s ∈ Ioo (0:ℝ) 1, ∀ i, Monotone (fun j =>
      (cutFullVariance n q U 0 0 b h K j i+t*cutTSlope n U 0 b h K j i)+
        s*(cutLSlope n U 0 b h K j i+t*cutLowError n U b h K j i)) := by
    intro s hs i
    have h := cutFullVariance_monotone n q U ⟨hs.1.le,hs.2.le⟩ ht hq hb hh hK hbm hhm hKm i
    rwa [cutFullVariance_biaffine] at h
  have hr : ∀ s ∈ Ioo (0:ℝ) 1, ∀ i, (0 : FullCoordinate n → ℝ) i ≤
      (cutFullVariance n q U 0 0 b h K 0 i+t*cutTSlope n U 0 b h K 0 i)+
        s*(cutLSlope n U 0 b h K 0 i+t*cutLowError n U b h K 0 i) := by
    intro s hs i
    have h := cutFullVariance_nonneg n q U ⟨hs.1.le,hs.2.le⟩ ht hq0 hb hh hK 0 i
    rw [cutFullVariance_biaffine] at h
    exact h
  have hd := ClockPolynomial.finiteLowJet_hasDerivAt_low (fullWeight_pos n) (fullFeature n)
    (T.testExpr P) ho 0
    (fun j i => cutFullVariance n q U 0 0 b h K j i+t*cutTSlope n U 0 b h K j i)
    (cutLSlope n U 0 b h K) (cutLowError n U b h K) k t hp hr hl x
  have he (s : ℝ) : (fun j i => cutFullVariance n q U 0 0 b h K j i+
      t*cutTSlope n U 0 b h K j i+s*(cutLSlope n U 0 b h K j i+t*cutLowError n U b h K j i)) =
      cutFullVariance n q U s t b h K := (cutFullVariance_biaffine n q U s t b h K).symm
  simp only [he] at hd
  exact hd

theorem cutLowJet_hasDerivAt_t (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) {l t : ℝ} (hl : l ∈ Icc (0:ℝ) 1) (ht : t ∈ Ioo (0:ℝ) 1)
    (b h K : ℕ → ℝ) (hq0 : ∀ j i, 0 ≤ q j i) (hq : ∀ i, Monotone (fun j => q j i))
    (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ) (k : ℕ) :
    HasDerivAt (cutLowJet n q U b h K T P x k l)
      (cutMixedJet n q U b h K T P x k l t) t := by
  have hp : ∀ s ∈ Ioo (0:ℝ) 1, ∀ i, Monotone (fun j =>
      cutFullVariance n q U 0 0 b h K j i+s*cutTSlope n U 0 b h K j i+
        l*(cutLSlope n U 0 b h K j i+s*cutLowError n U b h K j i)) := by
    intro s hs i
    have h := cutFullVariance_monotone n q U hl ⟨hs.1.le,hs.2.le⟩ hq hb hh hK hbm hhm hKm i
    rwa [cutFullVariance_biaffine] at h
  have hr : ∀ s ∈ Ioo (0:ℝ) 1, ∀ i, (0 : FullCoordinate n → ℝ) i ≤
      cutFullVariance n q U 0 0 b h K 0 i+s*cutTSlope n U 0 b h K 0 i+
        l*(cutLSlope n U 0 b h K 0 i+s*cutLowError n U b h K 0 i) := by
    intro s hs i
    have h := cutFullVariance_nonneg n q U hl ⟨hs.1.le,hs.2.le⟩ hq0 hb hh hK 0 i
    rw [cutFullVariance_biaffine] at h
    exact h
  have hd := ClockPolynomial.finiteLowJet_hasDerivAt_high (fullWeight_pos n) (fullFeature n)
    (T.testExpr P) ho 0 (cutFullVariance n q U 0 0 b h K)
    (cutLSlope n U 0 b h K) (cutTSlope n U 0 b h K) (cutLowError n U b h K) k l hp hr ht x
  have he (s : ℝ) : (fun j i => cutFullVariance n q U 0 0 b h K j i+
      s*cutTSlope n U 0 b h K j i+l*(cutLSlope n U 0 b h K j i+s*cutLowError n U b h K j i)) =
      cutFullVariance n q U l s b h K := (cutFullVariance_biaffine n q U l s b h K).symm
  simp only [he] at hd
  exact hd

 

theorem cutDisorderExpect_third_remainder (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (b h K : ℕ → ℝ) (hq0 : ∀ j i, 0 ≤ q j i) (hq : ∀ i, Monotone (fun j => q j i))
    (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 1 t b h K) P x =
      cutLowJet n q U b h K T P x 0 0 t+cutLowJet n q U b h K T P x 1 0 t+
      (1/2:ℝ)*cutLowJet n q U b h K T P x 2 0 t+
      (1/2:ℝ)*∫ l in (0:ℝ)..1, (1-l)^2*cutLowJet n q U b h K T P x 3 l t := by
  rw [← cutLowJet_zero n q U b h K T ho P x 1 t]
  apply third_low_remainder (fun l => cutLowJet n q U b h K T P x 0 l t)
    (fun l => cutLowJet n q U b h K T P x 1 l t)
    (fun l => cutLowJet n q U b h K T P x 2 l t)
    (fun l => cutLowJet n q U b h K T P x 3 l t)
  · exact cutLowJet_continuous_l n q U b h K T P x 0 t
  · exact cutLowJet_continuous_l n q U b h K T P x 1 t
  · exact cutLowJet_continuous_l n q U b h K T P x 2 t
  · exact cutLowJet_continuous_l n q U b h K T P x 3 t
  · intro l hl; exact cutLowJet_hasDerivAt_l n q U hl ht b h K hq0 hq hb hh hK hbm hhm hKm T ho P x 0
  · intro l hl; exact cutLowJet_hasDerivAt_l n q U hl ht b h K hq0 hq hb hh hK hbm hhm hKm T ho P x 1
  · intro l hl; exact cutLowJet_hasDerivAt_l n q U hl ht b h K hq0 hq hb hh hK hbm hhm hKm T ho P x 2

end SKFluctuations.Cavity

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 theorem ClockTree.disorderExpect_one {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (R : ClockTree S as)
    (ho : MassOrdered 0 as) (l : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    R.disorderExpect w φ l q (fun _ => 1) x = 1 := by
  simpa only [ClockTree.disorderExpect,mul_one] using (R.disorderWeight_probability hw φ ho l q x).2

end SKFluctuations.Hierarchy
namespace SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem cutFullVariance_scalar_endpoint (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (l : ℝ) (b h K : ℕ → ℝ) :
    cutFullVariance n q U l 0 b h K = fun j =>
      Sum.elim (Sum.elim (q j) (fun _ => relocatedClock U l K j)) (fun _ => 0) := by
  funext j i
  rcases i with (i | i) | (i | i) <;> simp [cutFullVariance,fullVariance]

 

theorem cutDisorderExpect_scalar_product (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (l : ℝ) (b h K : ℕ → ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment → ℝ) (Q : T.cavityRight.Assignment → ℝ)
    (x : ActiveCoordinate n → ℝ) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l 0 b h K)
      (fun σ => P (T.cavityAssignment σ).1*Q (T.cavityAssignment σ).2) (cavityEmbed x) =
      T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P (fun i => x (.inl i))*
      T.cavityRight.disorderExpect (fun _ : Bool => (1/2:ℝ)) scalarFeature 0
        (fun j _ => relocatedClock U l K j) Q (fun i => x (.inr i)) := by
  rw [cutFullVariance_scalar_endpoint]
  have hz : (0 : FullCoordinate n → ℝ) =
      Sum.elim (fun _ : ActiveCoordinate n => (0:ℝ)) (fun _ => 0) := by
    funext i; cases i <;> rfl
  rw [hz]
  rw [T.disorderExpect_zeroRow]
  simp only [fullFeature_restrict]
  exact T.disorderExpect_cavity_product (v := fun _ : Bool => (1/2:ℝ))
    (restWeight_pos n) (by intro s; norm_num) (restFeature n) scalarFeature ho 0
      (fun j => Sum.elim (q j) (fun _ => relocatedClock U l K j)) P Q x

 

theorem cutDisorderExpect_rest_endpoint (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (l : ℝ) (b h K : ℕ → ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment → ℝ) (x : ActiveCoordinate n → ℝ) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l 0 b h K)
      (fun σ => P (T.cavityAssignment σ).1) (cavityEmbed x) =
      T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P (fun i => x (.inl i)) := by
  have he := cutDisorderExpect_scalar_product n q U l b h K T ho P (fun _ => 1) x
  rw [T.cavityRight.disorderExpect_one (by intro s; norm_num) scalarFeature ho] at he
  simpa only [mul_one] using he

 

theorem cutDisorderExpect_site_endpoint (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (l : ℝ) (b h K : ℕ → ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (Q : T.cavityRight.Assignment → ℝ) (x : ActiveCoordinate n → ℝ) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l 0 b h K)
      (fun σ => Q (T.cavityAssignment σ).2) (cavityEmbed x) =
      T.cavityRight.disorderExpect (fun _ : Bool => (1/2:ℝ)) scalarFeature 0
        (fun j _ => relocatedClock U l K j) Q (fun i => x (.inr i)) := by
  have he := cutDisorderExpect_scalar_product n q U l b h K T ho (fun _ => 1) Q x
  rw [T.cavityLeft.disorderExpect_one (restWeight_pos n) (restFeature n) ho] at he
  simpa only [one_mul] using he

 
theorem cutDisorderExpect_centered_endpoint (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (l : ℝ) (b h K : ℕ → ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment → ℝ) (Q : T.cavityRight.Assignment → ℝ)
    (x : ActiveCoordinate n → ℝ) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l 0 b h K)
      (fun σ => P (T.cavityAssignment σ).1*Q (T.cavityAssignment σ).2) (cavityEmbed x) -
      T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l 0 b h K)
        (fun σ => Q (T.cavityAssignment σ).2) (cavityEmbed x)*
      T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l 0 b h K)
        (fun σ => P (T.cavityAssignment σ).1) (cavityEmbed x) = 0 := by
  rw [cutDisorderExpect_scalar_product n q U l b h K T ho,
    cutDisorderExpect_site_endpoint n q U l b h K T ho,
    cutDisorderExpect_rest_endpoint n q U l b h K T ho]
  ring

end SKFluctuations.Cavity

 

namespace SKFluctuations.Cavity
open MeasureTheory Filter Set
open scoped Topology

 
def productJet3 (g f : Fin 4 → ℝ) (k : Fin 4) : ℝ :=
  match k.val with
  | 0 => g 0*f 0
  | 1 => g 0*f 1+g 1*f 0
  | 2 => g 0*f 2+2*g 1*f 1+g 2*f 0
  | _ => g 0*f 3+3*g 1*f 2+3*g 2*f 1+g 3*f 0

 theorem productJet3_hasDerivAt (g f : Fin 4 → ℝ → ℝ) {l : ℝ}
    (hg : ∀ i : Fin 3, HasDerivAt (g i.castSucc) (g i.succ l) l)
    (hf : ∀ i : Fin 3, HasDerivAt (f i.castSucc) (f i.succ l) l) (k : Fin 3) :
    HasDerivAt (fun s => productJet3 (fun i => g i s) (fun i => f i s) k.castSucc)
      (productJet3 (fun i => g i l) (fun i => f i l) k.succ) l := by
  fin_cases k
  · convert (hg 0).mul (hf 0) using 1 <;> try rfl
    all_goals simp [productJet3]; ring
  · convert ((hg 0).mul (hf 1)).add ((hg 1).mul (hf 0)) using 1 <;>
      try rfl
    all_goals simp [productJet3]; ring
  · convert (((hg 0).mul (hf 2)).add (((hg 1).mul (hf 1)).const_mul 2)).add
      ((hg 2).mul (hf 0)) using 1 <;> try rfl
    all_goals (try funext s); simp [productJet3, Pi.mul_apply, Pi.add_apply]; ring

 theorem productJet3_hasDerivAt_right (g : Fin 4 → ℝ) (f : Fin 4 → ℝ → ℝ)
    (h : Fin 4 → ℝ) {t : ℝ} (hf : ∀ i, HasDerivAt (f i) (h i) t) (k : Fin 4) :
    HasDerivAt (fun s => productJet3 g (fun i => f i s) k) (productJet3 g h k) t := by
  fin_cases k
  · exact (hf 0).const_mul (g 0)
  · exact ((hf 1).const_mul (g 0)).add ((hf 0).const_mul (g 1))
  · exact (((hf 2).const_mul (g 0)).add ((hf 1).const_mul (2*g 1))).add
      ((hf 0).const_mul (g 2))
  · exact ((((hf 3).const_mul (g 0)).add ((hf 2).const_mul (3*g 1))).add
      ((hf 1).const_mul (3*g 2))).add ((hf 0).const_mul (g 3))

 theorem productJet3_continuous {X : Type*} [TopologicalSpace X]
    (g f : Fin 4 → X → ℝ) (hg : ∀ i, Continuous (g i)) (hf : ∀ i, Continuous (f i))
    (k : Fin 4) : Continuous (fun x => productJet3 (fun i => g i x) (fun i => f i x) k) := by
  fin_cases k <;> dsimp [productJet3] <;> fun_prop

 theorem derivative_zero_of_zero (f g : ℝ → ℝ)
    (hd : ∀ l ∈ Ioo (0:ℝ) 1, HasDerivAt f (g l) l)
    (hz : ∀ l ∈ Ioo (0:ℝ) 1, f l = 0) : ∀ l ∈ Ioo (0:ℝ) 1, g l = 0 := by
  intro l hl
  apply (hd l hl).unique
  apply (hasDerivAt_const l (0:ℝ)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hl] with s hs
  exact hz s hs

 

theorem thirdJet_zero_of_zero (f : Fin 4 → ℝ → ℝ) (hc : ∀ i, Continuous (f i))
    (hd : ∀ i : Fin 3, ∀ l ∈ Ioo (0:ℝ) 1, HasDerivAt (f i.castSucc) (f i.succ l) l)
    (hz : ∀ l ∈ Ioo (0:ℝ) 1, f 0 l = 0) :
    ∀ i : Fin 4, ∀ l ∈ Icc (0:ℝ) 1, f i l = 0 := by
  have h1 := derivative_zero_of_zero (f 0) (f 1) (hd 0) hz
  have h2 := derivative_zero_of_zero (f 1) (f 2) (hd 1) h1
  have h3 := derivative_zero_of_zero (f 2) (f 3) (hd 2) h2
  have hi (i : Fin 4) : EqOn (f i) (fun _ => 0) (Ioo (0:ℝ) 1) := by
    fin_cases i <;> assumption
  intro i l hl
  have he := (hi i).closure (hc i) continuous_const
  rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)] at he
  exact he hl

end SKFluctuations.Cavity

 

namespace SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy GaussianCalculus
open scoped Topology NNReal BigOperators

section
variable (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
  {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as)
  (P : T.cavityLeft.Assignment → ℝ) (Q : T.cavityRight.Assignment → ℝ)
  (x : ActiveCoordinate n → ℝ)

 
def cutCenteredJet (k : Fin 4) (l t : ℝ) : ℝ :=
  cutLowJet n q U b h K T (fun σ => P (T.cavityAssignment σ).1*Q (T.cavityAssignment σ).2)
      (cavityEmbed x) k l t -
    productJet3
      (fun i => cutLowJet n q U b h K T (fun σ => Q (T.cavityAssignment σ).2) (cavityEmbed x) i l 0)
      (fun i => cutLowJet n q U b h K T (fun σ => P (T.cavityAssignment σ).1) (cavityEmbed x) i l t) k

 
def cutCenteredMixedJet (k : Fin 4) (l t : ℝ) : ℝ :=
  cutMixedJet n q U b h K T (fun σ => P (T.cavityAssignment σ).1*Q (T.cavityAssignment σ).2)
      (cavityEmbed x) k l t -
    productJet3
      (fun i => cutLowJet n q U b h K T (fun σ => Q (T.cavityAssignment σ).2) (cavityEmbed x) i l 0)
      (fun i => cutMixedJet n q U b h K T (fun σ => P (T.cavityAssignment σ).1) (cavityEmbed x) i l t) k

 theorem cutCenteredJet_continuous_l (k : Fin 4) (t : ℝ) :
    Continuous (fun l => cutCenteredJet n q U b h K T P Q x k l t) := by
  apply (cutLowJet_continuous_l n q U b h K T _ _ _ _).sub
  exact productJet3_continuous _ _
    (fun _ => cutLowJet_continuous_l n q U b h K T _ _ _ _)
    (fun _ => cutLowJet_continuous_l n q U b h K T _ _ _ _) k

 theorem cutCenteredJet_continuous_t (k : Fin 4) (l : ℝ) :
    Continuous (cutCenteredJet n q U b h K T P Q x k l) := by
  apply (cutLowJet_continuous_t n q U b h K T _ _ _ _).sub
  exact productJet3_continuous _ _ (fun _ => continuous_const)
    (fun _ => cutLowJet_continuous_t n q U b h K T _ _ _ _) k

 theorem cutCenteredMixedJet_continuous_t (k : Fin 4) (l : ℝ) :
    Continuous (cutCenteredMixedJet n q U b h K T P Q x k l) := by
  apply (cutMixedJet_continuous_t n q U b h K T _ _ _ _).sub
  exact productJet3_continuous _ _ (fun _ => continuous_const)
    (fun _ => cutMixedJet_continuous_t n q U b h K T _ _ _ _) k

variable (hq0 : ∀ j i, 0 ≤ q j i) (hq : ∀ i, Monotone (fun j => q j i))
  (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j)
  (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
  (ho : MassOrdered 0 as)
include hq0 hq hb hh hK hbm hhm hKm ho

 theorem cutCenteredJet_hasDerivAt_l (k : Fin 3) {l t : ℝ}
    (hl : l ∈ Ioo (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun s => cutCenteredJet n q U b h K T P Q x k.castSucc s t)
      (cutCenteredJet n q U b h K T P Q x k.succ l t) l := by
  apply (cutLowJet_hasDerivAt_l n q U hl ht b h K hq0 hq hb hh hK hbm hhm hKm T ho _ _ _).sub
  exact productJet3_hasDerivAt _ _
    (fun _ => cutLowJet_hasDerivAt_l n q U hl (by norm_num) b h K hq0 hq hb hh hK hbm hhm hKm T ho _ _ _)
    (fun _ => cutLowJet_hasDerivAt_l n q U hl ht b h K hq0 hq hb hh hK hbm hhm hKm T ho _ _ _) k

 theorem cutCenteredJet_hasDerivAt_t (k : Fin 4) {l t : ℝ}
    (hl : l ∈ Icc (0:ℝ) 1) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (cutCenteredJet n q U b h K T P Q x k l)
      (cutCenteredMixedJet n q U b h K T P Q x k l t) t := by
  apply (cutLowJet_hasDerivAt_t n q U hl ht b h K hq0 hq hb hh hK hbm hhm hKm T ho _ _ _).sub
  exact productJet3_hasDerivAt_right _ _ _
    (fun _ => cutLowJet_hasDerivAt_t n q U hl ht b h K hq0 hq hb hh hK hbm hhm hKm T ho _ _ _) k

 theorem cutCenteredJet_zero_endpoint (k : Fin 4) {l : ℝ} (hl : l ∈ Icc (0:ℝ) 1) :
    cutCenteredJet n q U b h K T P Q x k l 0 = 0 := by
  apply thirdJet_zero_of_zero (fun k l => cutCenteredJet n q U b h K T P Q x k l 0)
    (fun _ => cutCenteredJet_continuous_l n q U b h K T P Q x _ 0)
    (fun _ _ hl => cutCenteredJet_hasDerivAt_l n q U b h K T P Q x hq0 hq hb hh hK hbm hhm hKm ho _ hl (by norm_num))
    _ k l hl
  intro s hs
  simp only [cutCenteredJet, productJet3, Fin.val_zero]
  simp only [cutLowJet_zero n q U b h K T ho]
  exact cutDisorderExpect_centered_endpoint n q U s b h K T ho P Q x

 

theorem cutCenteredJet_third_mixed_remainder :
    cutCenteredJet n q U b h K T P Q x 0 1 1 =
      cutCenteredJet n q U b h K T P Q x 0 0 1+
      cutCenteredJet n q U b h K T P Q x 1 0 1+
      (1/2:ℝ)*cutCenteredJet n q U b h K T P Q x 2 0 1+
      (1/2:ℝ)*∫ l in (0:ℝ)..1, (1-l)^2*∫ t in (0:ℝ)..1,
        cutCenteredMixedJet n q U b h K T P Q x 3 l t := by
  apply third_low_mixed_remainder
    (fun l => cutCenteredJet n q U b h K T P Q x 0 l 1)
    (fun l => cutCenteredJet n q U b h K T P Q x 1 l 1)
    (fun l => cutCenteredJet n q U b h K T P Q x 2 l 1)
    (cutCenteredJet n q U b h K T P Q x 3)
    (cutCenteredMixedJet n q U b h K T P Q x 3)
  · exact cutCenteredJet_continuous_l n q U b h K T P Q x 0 1
  · exact cutCenteredJet_continuous_l n q U b h K T P Q x 1 1
  · exact cutCenteredJet_continuous_l n q U b h K T P Q x 2 1
  · exact cutCenteredJet_continuous_l n q U b h K T P Q x 3 1
  · intro l _; exact cutCenteredJet_continuous_t n q U b h K T P Q x 3 l
  · intro l _; exact cutCenteredMixedJet_continuous_t n q U b h K T P Q x 3 l
  · intro l hl; exact cutCenteredJet_hasDerivAt_l n q U b h K T P Q x hq0 hq hb hh hK hbm hhm hKm ho 0 hl (by norm_num)
  · intro l hl; exact cutCenteredJet_hasDerivAt_l n q U b h K T P Q x hq0 hq hb hh hK hbm hhm hKm ho 1 hl (by norm_num)
  · intro l hl; exact cutCenteredJet_hasDerivAt_l n q U b h K T P Q x hq0 hq hb hh hK hbm hhm hKm ho 2 hl (by norm_num)
  · intro l hl t ht; exact cutCenteredJet_hasDerivAt_t n q U b h K T P Q x hq0 hq hb hh hK hbm hhm hKm ho 3 hl ht
  · intro l hl; exact cutCenteredJet_zero_endpoint n q U b h K T P Q x hq0 hq hb hh hK hbm hhm hKm ho 3 hl

end
end SKFluctuations.Cavity

 

namespace SKFluctuations.Cavity
open MeasureTheory Filter Set
open scoped Topology

 theorem second_jet_remainder (f₀ f₁ f₂ : ℝ → ℝ)
    (h₀ : Continuous f₀) (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (hd₀ : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt f₀ (f₁ t) t)
    (hd₁ : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt f₁ (f₂ t) t) :
    f₀ 1 = f₀ 0+f₁ 0+∫ t in (0:ℝ)..1, (1-t)*f₂ t := by
  let F := fun t => f₀ t+(1-t)*f₁ t
  have hc : Continuous F := by unfold F; fun_prop
  have hd (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : HasDerivAt F ((1-t)*f₂ t) t := by
    have hs : HasDerivAt (fun s : ℝ => 1-s) (-1) t := by
      convert (hasDerivAt_id t).const_sub 1 using 1; rfl
    convert (hd₀ t ht).add (hs.mul (hd₁ t ht)) using 1; try rfl
    ring
  have hi : IntervalIntegrable (fun t => (1-t)*f₂ t) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ) ≤ 1)
    hc.continuousOn hd hi
  dsimp [F] at H
  norm_num at H
  linarith

 theorem first_jet_remainder (f₀ f₁ : ℝ → ℝ)
    (h₀ : Continuous f₀) (h₁ : Continuous f₁)
    (hd₀ : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt f₀ (f₁ t) t) :
    f₀ 1 = f₀ 0+∫ t in (0:ℝ)..1, f₁ t := by
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ) ≤ 1)
    h₀.continuousOn hd₀ (h₁.intervalIntegrable 0 1)
  linarith

end SKFluctuations.Cavity

 

namespace SKFluctuations.Hierarchy.ClockPolynomial
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty ι] {as : List PositiveMass}

 
def finiteIterInsert (P : ClockPolynomial S as) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (d : ℕ → ι → ℝ) : ℕ → ClockPolynomial S as
  | 0 => P
  | k+1 => (P.finiteIterInsert φ d k).finiteInsert φ d

end SKFluctuations.Hierarchy.ClockPolynomial

end

end OAI
