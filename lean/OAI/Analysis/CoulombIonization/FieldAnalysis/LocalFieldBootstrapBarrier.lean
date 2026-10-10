import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.LocalHistoryWeightsBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_LocalFieldBootstrap_barrier_scope

open Set Metric

lemma localHistory_field_bound {E₀ E : CoreObservationEnsemble} {y₀ : Space} {a Z lam : ℝ}
    {ha : 0 < a} (hsep : 12*a ≤ ‖y₀‖) (hm : E₀.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {n : ℕ} (hE : CoreLocalHistory E₀ y₀ a ha n E) (y : Space)
    (hy : y ∈ closedBall y₀ (localHistoryReach a n)) :
    E.fieldMoment Z lam y ≤ 2*packetFieldConstant^2*((1/a^4+1/a)^2+max (E₀.excess Z lam) 0/a+
      256*localHistoryCostScale a (E₀.countMoment y₀ (8*a)) (localFieldEnvelope E₀ y₀ a ha Z lam)/a)*
        ((n:ℝ)+2)^16 := by
  let u := localHistoryRadius a n
  have hu := localHistoryRadius_pos ha n
  let hr : 0 ≤ 2*u := by dsimp [u]; positivity
  let p := coreFirstRadialCut y hr hu
  let hp := coreFirstRadialCut_partition y hr hu
  have hn := CoreLocalHistory.center_nuclear_separation (ha := ha) hsep y hy
  have hu' := localHistoryRadius_le ha n
  have hv (x : Space) (hx : x ∈ ball y (2*u)) : (p 0).value x = 0 :=
    coreFirstRadialCut_core_zero y hr hu x (by simpa only [radialPatchCore,mem_ofPred_eq,not_le,mem_ball,dist_eq_norm] using hx)
  have hd (x : Space) (hx : x ∈ ball y (2*u)) (d : Fin 3) : lineDeriv ℝ (p 0).value x (spaceDirections d) = 0 :=
    coreFirstRadialCut_core_deriv_zero y hr hu x (by simpa only [radialPatchCore,mem_ofPred_eq,not_le,mem_ball,dist_eq_norm] using hx) d
  have hf := E.fieldMoment_le_observe_excess p hp y hu (by linarith) hv hd hZ hlam
  rw [hE.mass,hm,mul_one] at hf
  have he := localHistory_excess_bound hsep hm hZ hlam.le (CoreLocalHistory.observe hE y hy)
  have hc := localHistoryCostScale_nonneg a (E₀.countMoment y₀ (8*a))
    (localFieldEnvelope_nonneg E₀ y₀ ha hsep hm hZ hlam.le)
  have he' : (E.observe p hp).excess Z lam ≤ max (E₀.excess Z lam) 0+
      localHistoryCostScale a (E₀.countMoment y₀ (8*a)) (localFieldEnvelope E₀ y₀ a ha Z lam)*
        ((n:ℝ)+1)*((n:ℝ)+3)^8 := by
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℝ)+2 = 3 by norm_num] using
      he.trans (add_le_add (le_max_left (E₀.excess Z lam) 0) le_rfl)
  have hediv := (div_le_div_of_nonneg_right he' hu.le).trans
    (localHistoryRadius_energy ha (le_max_right _ _) hc n)
  have hall := mul_le_mul_of_nonneg_left (add_le_add (localHistoryRadius_packet ha n) hediv)
    (by positivity : 0 ≤ 2*packetFieldConstant^2)
  apply hf.trans
  convert hall using 1
  ring

lemma localFieldEnvelope_quadratic (E₀ : CoreObservationEnsemble) (y₀ : Space) {a Z lam : ℝ}
    (ha : 0 < a) (hsep : 12*a ≤ ‖y₀‖) (hm : E₀.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    (localFieldEnvelope E₀ y₀ a ha Z lam)^2 ≤
      2*packetFieldConstant^2*((1/a^4+1/a)^2+max (E₀.excess Z lam) 0/a+
        256*localizationIMSConstant*Real.sqrt (E₀.countMoment y₀ (8*a))/a^3)+
      (4096*packetFieldConstant^2*Real.sqrt (E₀.countMoment y₀ (8*a))/a)*
        localFieldEnvelope E₀ y₀ a ha Z lam := by
  let H := localFieldEnvelope E₀ y₀ a ha Z lam
  let C := localHistoryCostScale a (E₀.countMoment y₀ (8*a)) H
  let G := 2*packetFieldConstant^2*((1/a^4+1/a)^2+max (E₀.excess Z lam) 0/a+256*C/a)
  have hH : 0 ≤ H := localFieldEnvelope_nonneg E₀ y₀ ha hsep hm hZ hlam.le
  have hC : 0 ≤ C := localHistoryCostScale_nonneg _ _ hH
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hb (t : ℝ) (ht : t ∈ localHistoryFieldValues E₀ y₀ a ha Z lam) : t ≤ Real.sqrt G := by
    obtain ⟨n,E,hE,y,hy,rfl⟩ := ht
    have hh := localHistory_field_bound hsep hm hZ hlam hE y hy
    have hsq : (Real.sqrt (E.fieldMoment Z lam y)/((n:ℝ)+2)^8)^2 ≤ G := by
      rw [div_pow,Real.sq_sqrt (E.fieldMoment_nonneg Z lam y),←pow_mul]
      apply (div_le_iff₀ (by positivity)).2
      exact hh
    exact (Real.le_sqrt (by positivity) hG).2 hsq
  have hu : H ≤ Real.sqrt G := csSup_le (localHistoryFieldValues_nonempty E₀ y₀ ha Z lam) hb
  have hs := pow_le_pow_left₀ hH hu 2
  rw [Real.sq_sqrt hG] at hs
  convert hs using 1
  dsimp [G,C,H,localHistoryCostScale]
  field_simp [ha.ne']
  ring

theorem ensemble_local_field_estimate (E₀ : CoreObservationEnsemble) (y₀ : Space) {a Z lam : ℝ}
    (ha : 0 < a) (hsep : 12*a ≤ ‖y₀‖) (hm : E₀.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    E₀.fieldMoment Z lam y₀ ≤ 65536*(
      4*packetFieldConstant^2*((1/a^4+1/a)^2+max (E₀.excess Z lam) 0/a+
        256*localizationIMSConstant*Real.sqrt (E₀.countMoment y₀ (8*a))/a^3)+
      (4096*packetFieldConstant^2*Real.sqrt (E₀.countMoment y₀ (8*a))/a)^2) := by
  let H := localFieldEnvelope E₀ y₀ a ha Z lam
  let A := 2*packetFieldConstant^2*((1/a^4+1/a)^2+max (E₀.excess Z lam) 0/a+
        256*localizationIMSConstant*Real.sqrt (E₀.countMoment y₀ (8*a))/a^3)
  let D := 4096*packetFieldConstant^2*Real.sqrt (E₀.countMoment y₀ (8*a))/a
  have hs : H^2 ≤ A+D*H := localFieldEnvelope_quadratic E₀ y₀ ha hsep hm hZ hlam
  have hs' : H^2 ≤ 2*A+D^2 := by nlinarith [sq_nonneg (H-D)]
  have hh := localFieldEnvelope_bound hsep hm hZ hlam.le (CoreLocalHistory.initial (E₀ := E₀) (y₀ := y₀) (a := a) (ha := ha)) y₀
    (by simp [localHistoryReach])
  norm_num at hh
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hh 2
  rw [Real.sq_sqrt (E₀.fieldMoment_nonneg Z lam y₀)] at hsq
  have hfinal := hsq.trans (show (localFieldEnvelope E₀ y₀ a ha Z lam*256)^2 ≤ 65536*(2*A+D^2) by nlinarith [hs'])
  convert hfinal using 1
  dsimp [A,D]
  ring

end Work_LocalFieldBootstrap_barrier_scope

def localFieldScale (a D B : ℝ) : ℝ :=
  (1/a^4+1/a)^2+1/a^4+D/a+B/a^2

def localFieldUniversalConstant : ℝ := 65536*(4*packetFieldConstant^2+
  512*packetFieldConstant^2*localizationIMSConstant+(4096*packetFieldConstant^2)^2)

lemma localFieldUniversalConstant_pos : 0 < localFieldUniversalConstant := by
  have := packetFieldConstant_pos
  have := localizationIMSConstant_nonneg
  unfold localFieldUniversalConstant
  positivity

lemma localFieldScale_nonneg {a D B : ℝ} (ha : 0 < a) (hD : 0 ≤ D) (hB : 0 ≤ B) :
    0 ≤ localFieldScale a D B := by unfold localFieldScale; positivity

lemma sqrt_count_reciprocal_young {a B : ℝ} (_ha : 0 < a) (hB : 0 ≤ B) :
    2*Real.sqrt B/a^3 ≤ 1/a^4+B/a^2 := by
  have he : (Real.sqrt B/a)^2 = B/a^2 := by rw [div_pow,Real.sq_sqrt hB]
  have hp : (1/a^2)^2 = (1:ℝ)/a^4 := by ring
  calc
    2*Real.sqrt B/a^3 = 2*(Real.sqrt B/a)*(1/a^2) := by ring
    _ ≤ (Real.sqrt B/a)^2+(1/a^2)^2 := by nlinarith [sq_nonneg (Real.sqrt B/a-1/a^2)]
    _ = _ := by rw [he,hp]; ring

lemma localFieldScale_mono {a D D' B B' : ℝ} (ha : 0 < a) (hD : D ≤ D') (hB : B ≤ B') :
    localFieldScale a D B ≤ localFieldScale a D' B' := by
  unfold localFieldScale
  exact add_le_add (add_le_add le_rfl (div_le_div_of_nonneg_right hD ha.le))
    (div_le_div_of_nonneg_right hB (sq_nonneg a))

lemma field_explicit_bound_le_scale {a D B : ℝ} (ha : 0 < a) (hD : 0 ≤ D) (hB : 0 ≤ B) :
    65536*(4*packetFieldConstant^2*((1/a^4+1/a)^2+D/a+
        256*localizationIMSConstant*Real.sqrt B/a^3)+
      (4096*packetFieldConstant^2*Real.sqrt B/a)^2) ≤
        localFieldUniversalConstant*localFieldScale a D B := by
  let S := localFieldScale a D B
  have hP : 0 ≤ 1/a^4 := by positivity
  have hB' : 0 ≤ B/a^2 := by positivity
  have hD' : 0 ≤ D/a := by positivity
  have hX : 0 ≤ (1/a^4+1/a)^2 := sq_nonneg _
  have hS1 : (1/a^4+1/a)^2+D/a ≤ S := by dsimp [S,localFieldScale]; linarith
  have hS2 : 1/a^4+B/a^2 ≤ S := by dsimp [S,localFieldScale]; linarith
  have hS3 : B/a^2 ≤ S := by dsimp [S,localFieldScale]; linarith
  have hK := localizationIMSConstant_nonneg
  have hy := mul_le_mul_of_nonneg_left (sqrt_count_reciprocal_young ha hB)
    (show 0 ≤ 512*packetFieldConstant^2*localizationIMSConstant by positivity)
  have hterm : (4096*packetFieldConstant^2*Real.sqrt B/a)^2 =
      (4096*packetFieldConstant^2)^2*(B/a^2) := by
    rw [div_pow,mul_pow,Real.sq_sqrt hB]
    ring
  rw [hterm]
  have h1 := mul_le_mul_of_nonneg_left hS1 (show 0 ≤ 4*packetFieldConstant^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hS2 (show 0 ≤ 512*packetFieldConstant^2*localizationIMSConstant by positivity)
  have h3 := mul_le_mul_of_nonneg_left hS3 (sq_nonneg (4096*packetFieldConstant^2))
  change _ ≤ 65536*(4*packetFieldConstant^2+
    512*packetFieldConstant^2*localizationIMSConstant+(4096*packetFieldConstant^2)^2)*S
  calc
    _ = 65536*(4*packetFieldConstant^2*((1/a^4+1/a)^2+D/a)+
      512*packetFieldConstant^2*localizationIMSConstant*(2*Real.sqrt B/a^3)+
      (4096*packetFieldConstant^2)^2*(B/a^2)) := by ring
    _ ≤ 65536*(4*packetFieldConstant^2*S+
      512*packetFieldConstant^2*localizationIMSConstant*S+(4096*packetFieldConstant^2)^2*S) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 (hy.trans h2)) h3) (by norm_num)
    _ = _ := by ring

theorem ensemble_local_field_scale (E : CoreObservationEnsemble) (y : Space) {a Z lam : ℝ}
    (ha : 0 < a) (hsep : 12*a ≤ ‖y‖) (hm : E.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    E.fieldMoment Z lam y ≤ localFieldUniversalConstant*
      localFieldScale a (max (E.excess Z lam) 0) (E.countMoment y (8*a)) :=
  (ensemble_local_field_estimate E y ha hsep hm hZ hlam).trans
    (field_explicit_bound_le_scale ha (le_max_right _ _) (E.countMoment_nonneg y (8*a)))

end CoulombAtom

end

end OAI
