import Mathlib
import OAI.Probability.SKValue.Equations.BurgersMild
import OAI.Probability.SKValue.Equations.DuhamelJets
import OAI.Probability.SKValue.Equations.PolynomialObservable

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators ContDiff
namespace SKValue
lemma SmoothEvolution.jet_pde_ordered {T:ℝ} {γ:ℝ → ℝ} {V:ℝ → ℝ → ℝ}
    (h:SmoothEvolution T γ V) (hi:IntervalIntegrable γ volume 0 T)
    {a b:ℝ} (ha:0≤a) (hab:a≤b) (hb:b≤T) (n:ℕ) (x:ℝ) :
    iteratedDeriv n (deriv (V b)) x-iteratedDeriv n (deriv (V a)) x=
      -(1/2:ℝ)*(weightedFamilyIntegral a b (fun _ ↦ 1)
        (fun t ↦ iteratedDeriv (n+2) (deriv (V t))) x)-
      weightedFamilyIntegral a b γ
        (fun t ↦ iteratedDeriv n (fun y ↦ deriv (V t) y*deriv (deriv (V t)) y)) x := by
  have haT:a∈Icc (0:ℝ) T := ⟨ha,hab.trans hb⟩
  have hbT:b∈Icc (0:ℝ) T := ⟨ha.trans hab,hb⟩
  have hfg:=h.gradient_family
  have hG:=hfg.mul hfg.deriv
  have hiab:IntervalIntegrable γ volume a b := hi.mono_set (by
    rw [uIcc_of_le hab,uIcc_of_le (ha.trans haT.2)]
    exact Icc_subset_Icc ha hb)
  induction n generalizing x with
  | zero =>
    have hh:=h.gradient_pde a haT b hbT x
    have hci:IntervalIntegrable (fun t ↦ deriv (deriv (deriv (V t))) x) volume a b := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hab]
      exact (hfg.deriv.deriv.at_continuous x).mono (Icc_subset_Icc ha hb)
    have hpi:IntervalIntegrable (fun t ↦ γ t*(deriv (V t) x*deriv (deriv (V t)) x)) volume a b :=
      hiab.mul_continuousOn (by rw [uIcc_of_le hab];exact (hG.at_continuous x).mono (Icc_subset_Icc ha hb))
    rw [intervalIntegral.integral_add (hci.const_mul _) hpi,intervalIntegral.integral_const_mul] at hh
    simpa only [Nat.zero_add,weightedFamilyIntegral,iteratedDeriv_zero,
      show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,one_mul,neg_add_rev,
      neg_mul,sub_eq_add_neg,add_comm] using hh
  | succ n ih =>
    have hleft:=(((hfg.slices b hbT).iteratedDeriv n).smooth.differentiable (by norm_num) x).hasDerivAt.sub
      (((hfg.slices a haT).iteratedDeriv n).smooth.differentiable (by norm_num) x).hasDerivAt
    have hright:=((hfg.iteratedDeriv (n+2)).weightedFamilyIntegral_hasDerivAt
      (intervalIntegrable_const (c:=(1:ℝ))) ha hab hb x).const_mul (-(1/2:ℝ))
    have hright:=hright.sub ((hG.iteratedDeriv n).weightedFamilyIntegral_hasDerivAt hiab ha hab hb x)
    have hEq:(fun y ↦ iteratedDeriv n (deriv (V b)) y-iteratedDeriv n (deriv (V a)) y)=
      (fun y ↦ -(1/2:ℝ)*weightedFamilyIntegral a b (fun _ ↦ 1)
        (fun t ↦ iteratedDeriv (n+2) (deriv (V t))) y-
          weightedFamilyIntegral a b γ (fun t ↦ iteratedDeriv n
            (fun q ↦ deriv (V t) q*deriv (deriv (V t)) q)) y) := funext ih
    have he:=hleft.unique (hright.congr_of_eventuallyEq (Eventually.of_forall ih))
    simpa only [iteratedDeriv_succ,Nat.add_assoc] using he
end SKValue

end

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue
lemma SmoothEvolution.jet_time_hasDerivAt {T:ℝ} {γ:ℝ → ℝ} {V:ℝ → ℝ → ℝ}
    (h:SmoothEvolution T γ V) (hi:IntervalIntegrable γ volume 0 T)
    {t:ℝ} (ht:t∈Ioo (0:ℝ) T) (hγ:ContinuousAt γ t) (n:ℕ) (x:ℝ):
    HasDerivAt (fun s ↦ iteratedDeriv n (deriv (V s)) x)
      (-(1/2:ℝ)*iteratedDeriv (n+2) (deriv (V t)) x-
        γ t*iteratedDeriv n (fun y ↦ deriv (V t) y*deriv (deriv (V t)) y) x) t := by
  let A:=fun s ↦ iteratedDeriv (n+2) (deriv (V s)) x
  let B:=fun s ↦ iteratedDeriv n (fun y ↦ deriv (V s) y*deriv (deriv (V s)) y) x
  have hA:ContinuousOn A (Icc (0:ℝ) T) := h.continuous_jet (n+2) x
  have hB:ContinuousOn B (Icc (0:ℝ) T) :=
    ((h.gradient_family.mul h.gradient_family.deriv).iteratedDeriv n).at_continuous x
  have hT:0≤T:=ht.1.le.trans ht.2.le
  have hiA:IntervalIntegrable A volume 0 T := by
    apply ContinuousOn.intervalIntegrable;simpa only [uIcc_of_le hT] using hA
  have hiB:IntervalIntegrable (fun s ↦ γ s*B s) volume 0 T :=
    hi.mul_continuousOn (by simpa only [uIcc_of_le hT] using hB)
  have htT:t∈Icc (0:ℝ) T:=⟨ht.1.le,ht.2.le⟩
  have hn:=Icc_mem_nhds ht.1 ht.2
  have hsub:uIcc (0:ℝ) t⊆uIcc (0:ℝ) T:=by
    rw [uIcc_of_le ht.1.le,uIcc_of_le hT];exact Icc_subset_Icc le_rfl ht.2.le
  have hAi:IntegrableOn A (Icc (0:ℝ) T) volume := by
    simpa only [uIcc_of_le hT] using (intervalIntegrable_iff').mp hiA
  have hBi:IntegrableOn (fun s ↦ γ s*B s) (Icc (0:ℝ) T) volume := by
    simpa only [uIcc_of_le hT] using (intervalIntegrable_iff').mp hiB
  have hdA:=intervalIntegral.integral_hasDerivAt_right (hiA.mono_set hsub)
    ⟨Icc (0:ℝ) T,hn,hAi.aestronglyMeasurable⟩ ((hA t htT).continuousAt hn)
  have hdB:=intervalIntegral.integral_hasDerivAt_right (hiB.mono_set hsub)
    ⟨Icc (0:ℝ) T,hn,hBi.aestronglyMeasurable⟩ (hγ.mul ((hB t htT).continuousAt hn))
  have hd:=((hasDerivAt_const t (iteratedDeriv n (deriv (V 0)) x)).add
    (hdA.const_mul (-(1/2:ℝ)))).sub hdB
  simp only [zero_add] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [hn] with s hs
  have he:=h.jet_pde_ordered hi (a:=0) (by norm_num) hs.1 hs.2 n x
  dsimp only [weightedFamilyIntegral] at he
  simp only [one_mul] at he
  change iteratedDeriv n (deriv (V s)) x=
    iteratedDeriv n (deriv (V 0)) x+(-(1/2:ℝ))*(∫ r in (0:ℝ)..s,A r)-∫ r in (0:ℝ)..s,γ r*B r
  dsimp only [A,B]
  linarith
end SKValue

end

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue
namespace JetExpr
noncomputable def timeB (e:JetExpr):JetExpr := D (fun n ↦ mul (const (-1)) (coord (n+2))) e
noncomputable def timeP (e:JetExpr):JetExpr := D (fun n ↦ mul (const (-1)) ((mul (coord 0) (coord 1)).spatialIter n)) e
end JetExpr
lemma SmoothEvolution.polyJet_time_hasDerivAt {T:ℝ} {γ:ℝ → ℝ} {V:ℝ → ℝ → ℝ}
    (h:SmoothEvolution T γ V) (hi:IntervalIntegrable γ volume 0 T)
    {t:ℝ} (ht:t∈Ioo (0:ℝ) T) (hγ:ContinuousAt γ t) (e:JetExpr) (x:ℝ):
    HasDerivAt (fun s ↦ polyJet V e s x)
      ((1/2:ℝ)*polyJet V e.timeB t x+γ t*polyJet V e.timeP t x) t := by
  induction e with
  | const c => simpa only [polyJet,JetExpr.timeB,JetExpr.timeP,JetExpr.D,JetExpr.eval,mul_zero,add_zero] using hasDerivAt_const t c
  | coord n =>
    have hd:=h.jet_time_hasDerivAt hi ht hγ n x
    have he:=congrFun (h.polyJet_iterated (JetExpr.mul (.coord 0) (.coord 1)) ⟨ht.1.le,ht.2.le⟩ n) x
    have hf:polyJet V (JetExpr.mul (.coord 0) (.coord 1)) t=
        fun y ↦ deriv (V t) y*deriv (deriv (V t)) y := by
      funext y;simp only [polyJet,JetExpr.eval,iteratedDeriv_zero,iteratedDeriv_one]
    rw [hf] at he
    change _=JetExpr.eval (fun i ↦ iteratedDeriv i (deriv (V t)) x) _ at he
    simp only [polyJet,JetExpr.timeB,JetExpr.timeP,JetExpr.D,JetExpr.eval]
    rw [←he]
    convert hd using 1
    ring
  | add e f he hf =>
    convert he.add hf using 1 <;> (try (ext s; rfl))
    simp only [polyJet,JetExpr.timeB,JetExpr.timeP,JetExpr.D,JetExpr.eval]
    ring
  | mul e f he hf =>
    convert he.mul hf using 1 <;> (try (ext s; rfl))
    simp only [polyJet,JetExpr.timeB,JetExpr.timeP,JetExpr.D,JetExpr.eval]
    ring
lemma SmoothEvolution.polyJet_pde_ordered {T:ℝ} {γ:ℝ → ℝ} {V:ℝ → ℝ → ℝ}
    (h:SmoothEvolution T γ V) (hi:IntervalIntegrable γ volume 0 T)
    (hm:MonotoneOn γ (Icc (0:ℝ) T)) {a b:ℝ} (ha:0≤a) (hab:a≤b) (hb:b≤T)
    (e:JetExpr) (x:ℝ):
    polyJet V e b x-polyJet V e a x=∫ s in a..b,
      ((1/2:ℝ)*polyJet V e.timeB s x+γ s*polyJet V e.timeP s x) := by
  obtain ⟨L,hL,hl⟩:=(h.polyJet_joint e).joint
  have hLip:LipschitzOnWith (Real.toNNReal L) (fun s ↦ polyJet V e s x) (uIcc a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    rw [uIcc_of_le hab] at hs ht
    simpa only [Real.coe_toNNReal _ hL,Real.dist_eq,sub_self,abs_zero,add_zero] using
      hl t ⟨ha.trans ht.1,ht.2.trans hb⟩ s ⟨ha.trans hs.1,hs.2.trans hb⟩ x x
  rw [←hLip.absolutelyContinuousOnInterval.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [monotoneOn_ae_continuousAt_interior hm,(Set.countable_singleton b).ae_notMem volume] with s hs hsb hsi
  rw [uIoc_of_le hab] at hsi
  have hst:s<T := (lt_of_le_of_ne hsi.2 (by simpa only [mem_singleton_iff] using hsb)).trans_le hb
  exact (h.polyJet_time_hasDerivAt hi ⟨ha.trans_lt hsi.1,hst⟩ (hs ⟨ha.trans_lt hsi.1,hst⟩) e x).deriv
lemma SmoothEvolution.polyJet_pde {T:ℝ} {γ:ℝ → ℝ} {V:ℝ → ℝ → ℝ}
    (h:SmoothEvolution T γ V) (hi:IntervalIntegrable γ volume 0 T)
    (hm:MonotoneOn γ (Icc (0:ℝ) T)) {a b:ℝ} (ha:a∈Icc (0:ℝ) T) (hb:b∈Icc (0:ℝ) T)
    (e:JetExpr) (x:ℝ):
    polyJet V e b x-polyJet V e a x=∫ s in a..b,
      ((1/2:ℝ)*polyJet V e.timeB s x+γ s*polyJet V e.timeP s x) := by
  rcases le_total a b with hab|hab
  · exact h.polyJet_pde_ordered hi hm ha.1 hab hb.2 e x
  · rw [intervalIntegral.integral_symm]
    rw [←h.polyJet_pde_ordered hi hm hb.1 hab ha.2 e x]
    ring
end SKValue

end

end OAI
