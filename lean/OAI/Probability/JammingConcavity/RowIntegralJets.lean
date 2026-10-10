import Mathlib
import OAI.Probability.JammingConcavity.RowMixedCalculus

namespace OAI

/-! Row Integral Jets. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open Set Filter MeasureTheory
open scoped Topology

namespace MicroscopicJamming

lemma integral_hasDerivAt_of_jointly_continuous {F G : ℝ → ℝ → ℝ} {a b x : ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (uIcc a b ×ˢ univ))
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (uIcc a b ×ˢ univ))
    (hd : ∀ t∈uIcc a b,∀ y,HasDerivAt (F t) (G t y) y) :
    HasDerivAt (fun y => ∫ t in a..b,F t y) (∫ t in a..b,G t x) x := by
  have hfc (y : ℝ) : ContinuousOn (fun t => F t y) (uIcc a b) :=
    hF.comp (continuousOn_id.prodMk continuousOn_const) (fun t ht => ⟨ht,mem_univ _⟩)
  have hgc (y : ℝ) : ContinuousOn (fun t => G t y) (uIcc a b) :=
    hG.comp (continuousOn_id.prodMk continuousOn_const) (fun t ht => ⟨ht,mem_univ _⟩)
  have hcompact : IsCompact (uIcc a b ×ˢ Icc (x-1) (x+1)) := isCompact_uIcc.prod isCompact_Icc
  obtain ⟨M,hM⟩ := hcompact.exists_bound_of_continuousOn (hG.mono (prod_mono_right (subset_univ _)))
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=fun y t => F t y) (F':=fun y t => G t y) (s:=Icc (x-1) (x+1))
    (Icc_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall (fun y => ((hfc y).aestronglyMeasurable measurableSet_uIcc).mono_set uIoc_subset_uIcc))
    (hfc x).intervalIntegrable
    (((hgc x).aestronglyMeasurable measurableSet_uIcc).mono_set uIoc_subset_uIcc)
    (Eventually.of_forall (fun t ht y hy => hM (t,y) ⟨uIoc_subset_uIcc ht,hy⟩))
    (intervalIntegrable_const (c:=M))
    (Eventually.of_forall (fun t ht y _ => hd t (uIoc_subset_uIcc ht) y))).2

lemma iteratedDeriv_integral_of_jets {F : ℝ → ℝ → ℝ} {a b : ℝ}
    (hc : ∀ n : ℕ,ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv n (F p.1) p.2) (uIcc a b ×ˢ univ))
    (hs : ∀ t∈uIcc a b,ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F t)) :
    ∀ n : ℕ, iteratedDeriv n (fun y => ∫ t in a..b,F t y)=fun y => ∫ t in a..b,iteratedDeriv n (F t) y := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    exact (integral_hasDerivAt_of_jointly_continuous (hc n) (hc (n+1)) (fun t ht y => by
      have hd := ((contDiff_iff_iteratedDeriv.mp (hs t ht)).2 n (by simp) y).hasDerivAt
      simpa only [iteratedDeriv_succ] using hd)).deriv
end MicroscopicJamming

 
open Set Filter MeasureTheory
open scoped Topology

namespace MicroscopicJamming

lemma evolution_all_jets {Q : ℝ} (hQ : 0<Q) {F G : ℝ → ℝ → ℝ}
    (hcF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc 0 Q ×ˢ univ))
    (hcG : ∀ n : ℕ,ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv n (G p.1) p.2) (Icc 0 Q ×ˢ univ))
    (hsF : ∀ t∈Icc 0 Q,ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F t))
    (hsG : ∀ t∈Icc 0 Q,ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G t))
    (ht : ∀ t∈Ioo 0 Q,∀ x,HasDerivAt (fun r => F r x) (G t x) t) :
    ∀ n : ℕ,∀ t∈Ico 0 Q,∀ x,HasDerivWithinAt (fun r => iteratedDeriv n (F r) x)
      (iteratedDeriv n (G t) x) (Ici t) t := by
  have hsub (t : ℝ) (ht' : t∈Icc 0 Q) : uIcc t Q ⊆ Icc 0 Q := by
    rw [uIcc_of_le ht'.2]; exact Icc_subset_Icc ht'.1 le_rfl
  have heq (t : ℝ) (ht' : t∈Icc 0 Q) : (fun y => ∫ r in t..Q,G r y) = fun y => F Q y-F t y := by
    funext y
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht'.2
    · exact hcF.comp (continuousOn_id.prodMk continuousOn_const) (fun r hr => ⟨⟨ht'.1.trans hr.1,hr.2⟩,mem_univ _⟩)
    · exact fun r hr => ht r ⟨lt_of_le_of_lt ht'.1 hr.1,hr.2⟩ y
    · have hc : ContinuousOn (fun r => iteratedDeriv 0 (G r) y) (uIcc t Q) := (hcG 0).comp (continuousOn_id.prodMk continuousOn_const) (fun r hr => ⟨hsub t ht' hr,mem_univ _⟩)
      simpa only [iteratedDeriv_zero] using hc.intervalIntegrable
  have hjeq (n : ℕ) (t : ℝ) (ht' : t∈Icc 0 Q) (x : ℝ) :
      iteratedDeriv n (F t) x=iteratedDeriv n (F Q) x-∫ r in t..Q,iteratedDeriv n (G r) x := by
    have hh := congrFun (iteratedDeriv_integral_of_jets
      (fun n => (hcG n).mono (prod_mono_left (hsub t ht')))
      (fun r hr => hsG r (hsub t ht' hr)) n) x
    rw [heq t ht'] at hh
    rw [iteratedDeriv_fun_sub ((hsF Q ⟨hQ.le,le_rfl⟩).of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))).contDiffAt
      ((hsF t ht').of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))).contDiffAt] at hh
    linarith
  intro n t htt x
  let E : ℝ → ℝ := fun r => iteratedDeriv n (G (projIcc 0 Q hQ.le r)) x
  have hE : Continuous E := by
    apply ((continuousOn_iff_continuous_domRestrict.mp ((hcG n).comp
      (continuousOn_id.prodMk continuousOn_const) (fun r hr => ⟨hr,mem_univ _⟩))).comp (continuous_projIcc (h:=hQ.le)))
  have hEe (r : ℝ) (hr : r∈Icc 0 Q) : E r=iteratedDeriv n (G r) x := by
    dsimp only [E]; rw [projIcc_of_mem hQ.le hr]
  have hder := (intervalIntegral.integral_hasDerivAt_left (hE.intervalIntegrable t Q)
    hE.aestronglyMeasurable.stronglyMeasurableAtFilter hE.continuousAt).const_sub (iteratedDeriv n (F Q) x)
  have hder' : HasDerivWithinAt (fun r => iteratedDeriv n (F Q) x-∫ s in r..Q,E s)
      (iteratedDeriv n (G t) x) (Ici t) t := by
    simpa only [neg_neg,hEe t ⟨htt.1,htt.2.le⟩] using hder.hasDerivWithinAt (s:=Ici t)
  apply hder'.congr_of_eventuallyEq
  · filter_upwards [Icc_mem_nhdsGE htt.2] with r hr
    have hr' : r∈Icc 0 Q := ⟨htt.1.trans hr.1,hr.2⟩
    rw [hjeq n r hr']
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    exact (hEe s ((hsub r hr') hs)).symm
  · rw [hjeq n t ⟨htt.1,htt.2.le⟩]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    exact (hEe s ((hsub t ⟨htt.1,htt.2.le⟩) hs)).symm
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
namespace Higher

lemma sum_linear_jet_decompose (n : ℕ) (b u : ℕ → ℝ) :
    (∑ i∈Finset.range (n+2),((n+1).choose i:ℝ)*b i*u (n+1-i+1)) =
      b 0*u (n+2)+(n+1)*b 1*u (n+1)+
        ∑ j∈Finset.range n,((n+1).choose (j+2):ℝ)*b (j+2)*u (n-j) := by
  rw [show n+2=n+1+1 by omega,Finset.sum_range_succ',Finset.sum_range_succ']
  simp only [Nat.choose_zero_right,Nat.cast_one,one_mul,Nat.sub_zero,Nat.choose_one_right,
    Nat.cast_add,Nat.cast_one,Nat.zero_add,Nat.sub_add_cancel (by omega : 1≤n+1)]
  have he : (∑ j∈Finset.range n,((n+1).choose (j+1+1):ℝ)*b (j+1+1)*u (n+1-(j+1+1)+1)) =
      ∑ j∈Finset.range n,((n+1).choose (j+2):ℝ)*b (j+2)*u (n-j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hh := Finset.mem_range.mp hj
    have ha : n+1-(j+1+1)+1=n-j := by omega
    simp only [ha,Nat.add_assoc]
  rw [he]
  ring

lemma family_linear_bound {ι : Type*} {P : ι → Prop} {Q K R A : ℝ}
    (hQ : 0<Q) (hK : 0≤K) (hR : 0≤R) (hA : 0≤A)
    {U b d r a H : ι → ℝ → ℝ → ℝ}
    (hc : ∀ i,P i → ContinuousOn (fun p : ℝ × ℝ => U i p.1 p.2) (Icc 0 Q ×ˢ univ))
    (hx : ∀ i,P i → ∀ t∈Icc 0 Q,Differentiable ℝ (U i t) ∧ Differentiable ℝ (deriv (U i t)))
    (ht : ∀ i,P i → ∀ t∈Ico 0 Q,∀ x,HasDerivWithinAt (fun s => U i s x) (d i t x) (Ici t) t)
    (ha : ∀ i,P i → ∀ t∈Icc 0 Q,∀ x,0≤a i t x ∧ a i t x≤A)
    (hb : ∀ i,P i → ∀ t∈Icc 0 Q,∀ x,|b i t x|≤K*(1+|x|))
    (hr : ∀ i,P i → ∀ t∈Ico 0 Q,∀ x,r i t x≤R)
    (hg : ∀ i,P i → UniformPolynomialGrowth (Icc 0 Q) (U i))
    (hH : FamilyGrowth P (Icc 0 Q) H)
    (hp : ∀ i,P i → ∀ t∈Ico 0 Q,∀ x,
      d i t x+a i t x*deriv (deriv (U i t)) x+b i t x*deriv (U i t) x+r i t x*U i t x=H i t x)
    (hterm : ∀ i,P i → ∀ x,U i Q x=0) : FamilyGrowth P (Icc 0 Q) U := by
  obtain ⟨n,C,hC,hbd⟩ := hH.polynomial_source
  let g := R+(4*A*(n+2)^2+4*K*(n+2)+1)+1
  have hg0 : 0≤g := by dsimp [g]; positivity
  refine ⟨2*(n+2),C*Real.exp (g*Q),by positivity,fun i hi t htt x => ?_⟩
  have hu := VariableDiffusion.backward_polynomial_source_bound n hQ hK hA hR (le_refl 0) hC
    (hc i hi) (hx i hi) (ht i hi) (ha i hi) (hb i hi) (hg i hi) (hr i hi)
    (fun t htt x => by rw [hp i hi t htt x]; exact hbd i hi t ⟨htt.1,htt.2.le⟩ x)
    (fun x => by rw [hterm i hi x]; simp)
  have hpw : (1+x^2)^(n+2) ≤ (1+|x|)^(2*(n+2)) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [sq_abs x,abs_nonneg x]
  calc
    |U i t x| ≤ polynomialBarrier n (0+C) g Q t x := hu t htt x
    _ = C*Real.exp (g*(Q-t))*(1+x^2)^(n+2) := by simp [polynomialBarrier]
    _ ≤ C*Real.exp (g*Q)*(1+|x|)^(2*(n+2)) := by
      apply mul_le_mul _ hpw (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_left _ hC
      exact Real.exp_le_exp.mpr (by nlinarith [htt.1])

lemma linear_all_jets_growth {ι : Type*} {P : ι → Prop} {Q K A : ℝ}
    (hQ : 0<Q) (hK : 0≤K) (hA : 0≤A)
    {U b H : ι → ℝ → ℝ → ℝ} {a : ι → ℝ → ℝ}
    (hs : ∀ i,P i → JointSpatialSmooth (Icc 0 Q) (U i))
    (ha : ∀ i,P i → ∀ t∈Icc 0 Q,0≤a i t ∧ a i t≤A)
    (hb : ∀ i,P i → ∀ t∈Icc 0 Q,∀ x,|b i t x|≤K*(1+|x|))
    (hbb : ∀ n : ℕ,1≤n → ∃ B : ℝ,0≤B ∧ ∀ i,P i → ∀ t∈Icc 0 Q,∀ x,|iteratedDeriv n (b i t) x|≤B)
    (hg : ∀ i,P i → ∀ n : ℕ,UniformPolynomialGrowth (Icc 0 Q) (fun t => iteratedDeriv n (U i t)))
    (hH : ∀ n : ℕ,FamilyGrowth P (Icc 0 Q) (fun i t => iteratedDeriv n (H i t)))
    (ht : ∀ i,P i → ∀ n : ℕ,∀ t∈Ico 0 Q,∀ x,HasDerivWithinAt (fun s => iteratedDeriv n (U i s) x)
      (iteratedDeriv n (H i t) x-a i t*iteratedDeriv (n+2) (U i t) x-
        ∑ j∈Finset.range (n+1),(n.choose j:ℝ)*iteratedDeriv j (b i t) x*iteratedDeriv (n-j+1) (U i t) x)
      (Ici t) t)
    (hterm : ∀ i,P i → ∀ x,U i Q x=0) :
    ∀ n : ℕ,FamilyGrowth P (Icc 0 Q) (fun i t => iteratedDeriv n (U i t)) := by
  have hd (i : ι) (hi : P i) (n : ℕ) (t : ℝ) (htt : t∈Icc 0 Q) :
      Differentiable ℝ (iteratedDeriv n (U i t)) :=
    (contDiff_iff_iteratedDeriv.mp ((hs i hi).1 t htt)).2 n (by simp)
  have htermj (i : ι) (hi : P i) (n : ℕ) (x : ℝ) : iteratedDeriv n (U i Q) x=0 := by
    have he : U i Q=fun _ => 0 := funext (hterm i hi)
    rw [he]
    simp
  intro n
  induction n using Nat.strong_induction_on with
  | h N ih =>
    let D : ι → ℝ → ℝ → ℝ := fun i t x => iteratedDeriv N (H i t) x-a i t*iteratedDeriv (N+2) (U i t) x-
      ∑ j∈Finset.range (N+1),(N.choose j:ℝ)*iteratedDeriv j (b i t) x*iteratedDeriv (N-j+1) (U i t) x
    have hhx (i : ι) (hi : P i) (t : ℝ) (htt : t∈Icc 0 Q) :
        Differentiable ℝ (iteratedDeriv N (U i t)) ∧ Differentiable ℝ (deriv (iteratedDeriv N (U i t))) := by
      exact ⟨hd i hi N t htt,by simpa only [←iteratedDeriv_succ] using hd i hi (N+1) t htt⟩
    cases N with
    | zero =>
      apply family_linear_bound (d:=D) (r:=fun _ _ _ => 0) (a:=fun i t _ => a i t)
        hQ hK (le_refl 0) hA (fun i hi => (hs i hi).2 0) hhx
        (fun i hi => ht i hi 0) (fun i hi t htt _ => ha i hi t htt) hb
        (fun _ _ _ _ _ => le_refl 0) (fun i hi => hg i hi 0) (hH 0) _ (fun i hi => htermj i hi 0)
      intro i hi t htt x
      simp [D,iteratedDeriv_succ]
      ring
    | succ n =>
      obtain ⟨B,hB,hbd⟩ := hbb 1 (by omega)
      let E : ι → ℝ → ℝ → ℝ := fun i t x => iteratedDeriv (n+1) (H i t) x-
        ∑ j∈Finset.range n,((n+1).choose (j+2):ℝ)*iteratedDeriv (j+2) (b i t) x*iteratedDeriv (n-j) (U i t) x
      have hE : FamilyGrowth P (Icc 0 Q) E := by
        apply (hH (n+1)).sub
        apply FamilyGrowth.finset_sum
        intro j hj
        obtain ⟨B',hB',hbd'⟩ := hbb (j+2) (by omega)
        exact ((FamilyGrowth.of_bound hB' hbd').const_mul ((n+1).choose (j+2):ℝ)).mul
          (ih (n-j) (by omega))
      apply family_linear_bound (d:=D) (r:=fun i t x => (n+1)*iteratedDeriv 1 (b i t) x)
        (a:=fun i t _ => a i t) hQ hK (show 0≤((n:ℝ)+1)*B by positivity) hA
        (fun i hi => (hs i hi).2 (n+1)) hhx (fun i hi => ht i hi (n+1))
        (fun i hi t htt _ => ha i hi t htt) hb _ (fun i hi => hg i hi (n+1)) hE _ (fun i hi => htermj i hi (n+1))
      · intro i hi t htt x
        exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hbd i hi t ⟨htt.1,htt.2.le⟩ x)) (by positivity)
      · intro i hi t htt x
        dsimp [D,E]
        rw [sum_linear_jet_decompose n (fun j => iteratedDeriv j (b i t) x) (fun j => iteratedDeriv j (U i t) x)]
        simp only [iteratedDeriv_zero,←iteratedDeriv_succ]
        ring
end Higher
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
namespace Higher

lemma JointSpatialSmooth.sub {S : Set ℝ} {F G : ℝ → ℝ → ℝ}
    (hf : JointSpatialSmooth S F) (hg : JointSpatialSmooth S G) :
    JointSpatialSmooth S (fun t x => F t x-G t x) := by
  simpa only [neg_one_mul,sub_eq_add_neg] using hf.add (hg.coeff_mul (a:=fun _ => -1) continuousOn_const)

lemma linear_evolution_jets {Q : ℝ} (hQ : 0<Q) {U b H : ℝ → ℝ → ℝ} {a : ℝ → ℝ}
    (hs : JointSpatialSmooth (Icc 0 Q) U) (hb : JointSpatialSmooth (Icc 0 Q) b)
    (hH : JointSpatialSmooth (Icc 0 Q) H) (ha : ContinuousOn a (Icc 0 Q))
    (ht : ∀ t∈Ioo 0 Q,∀ x,HasDerivAt (fun s => U s x)
      (H t x-a t*iteratedDeriv 2 (U t) x-b t x*iteratedDeriv 1 (U t) x) t) :
    ∀ n : ℕ,∀ t∈Ico 0 Q,∀ x,HasDerivWithinAt (fun s => iteratedDeriv n (U s) x)
      (iteratedDeriv n (H t) x-a t*iteratedDeriv (n+2) (U t) x-
        ∑ j∈Finset.range (n+1),(n.choose j:ℝ)*iteratedDeriv j (b t) x*iteratedDeriv (n-j+1) (U t) x)
      (Ici t) t := by
  have hG := (hH.sub ((hs.jet 2).coeff_mul ha)).sub (hb.mul (hs.jet 1))
  have hh := evolution_all_jets hQ (by simpa using hs.2 0) hG.2 hs.1 hG.1 ht
  intro n t htt x
  have htcc : t∈Icc 0 Q := ⟨htt.1,htt.2.le⟩
  have hUn (k : ℕ) : ContDiff ℝ (n:WithTop ℕ∞) (iteratedDeriv k (U t)) :=
    ((hs.jet k).1 t htcc).of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))
  have hbn : ContDiff ℝ (n:WithTop ℕ∞) (b t) :=
    (hb.1 t htcc).of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))
  have hHn : ContDiff ℝ (n:WithTop ℕ∞) (H t) :=
    (hH.1 t htcc).of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))
  convert hh n t htt x using 1
  symm
  rw [iteratedDeriv_fun_sub (hHn.sub (contDiff_const.mul (hUn 2))).contDiffAt (hbn.mul (hUn 1)).contDiffAt]
  rw [iteratedDeriv_fun_sub hHn.contDiffAt (contDiff_const.mul (hUn 2)).contDiffAt]
  rw [iteratedDeriv_const_mul_field,iteratedDeriv_fun_mul hbn.contDiffAt (hUn 1).contDiffAt]
  simp only [iteratedDeriv_iteratedDeriv]

end Higher
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
namespace Higher

structure PolynomialJetFamily {ι : Type*} (P : ι → Prop) (T : Set ℝ)
    (F : ι → ℝ → ℝ → ℝ) : Prop where
  smooth : ∀ i,P i → JointSpatialSmooth T (F i)
  bounds : ∀ n : ℕ,FamilyGrowth P T (fun i t => iteratedDeriv n (F i t))

lemma PolynomialJetFamily.jet {ι : Type*} {P : ι → Prop} {T : Set ℝ} {F : ι → ℝ → ℝ → ℝ}
    (hf : PolynomialJetFamily P T F) (n : ℕ) :
    PolynomialJetFamily P T (fun i t => iteratedDeriv n (F i t)) := by
  refine ⟨fun i hi => (hf.smooth i hi).jet n,fun k => ?_⟩
  simpa only [iteratedDeriv_iteratedDeriv] using hf.bounds (k+n)

lemma PolynomialJetFamily.comp {ι κ : Type*} {P : ι → Prop} {R : κ → Prop} {T : Set ℝ}
    {F : ι → ℝ → ℝ → ℝ} (hf : PolynomialJetFamily P T F) (g : κ → ι) (hg : ∀ i,R i → P (g i)) :
    PolynomialJetFamily R T (fun i => F (g i)) :=
  ⟨fun i hi => hf.smooth (g i) (hg i hi),fun n => (hf.bounds n).comp g hg⟩

lemma PolynomialJetFamily.add {ι : Type*} {P : ι → Prop} {T : Set ℝ} {F G : ι → ℝ → ℝ → ℝ}
    (hf : PolynomialJetFamily P T F) (hg : PolynomialJetFamily P T G) :
    PolynomialJetFamily P T (fun i t x => F i t x+G i t x) := by
  refine ⟨fun i hi => (hf.smooth i hi).add (hg.smooth i hi),fun n => ?_⟩
  apply ((hf.bounds n).add (hg.bounds n)).congr
  intro i hi t ht x
  exact (iteratedDeriv_fun_add ((hf.smooth i hi).1 t ht |>.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))).contDiffAt
    ((hg.smooth i hi).1 t ht |>.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))).contDiffAt).symm

lemma PolynomialJetFamily.coeff_mul {ι : Type*} {P : ι → Prop} {T : Set ℝ}
    {F : ι → ℝ → ℝ → ℝ} {a : ι → ℝ → ℝ}
    (hf : PolynomialJetFamily P T F) (ha : ∀ i,P i → ContinuousOn (a i) T)
    {A : ℝ} (hA : 0≤A) (hab : ∀ i,P i → ∀ t∈T,|a i t|≤A) :
    PolynomialJetFamily P T (fun i t x => a i t*F i t x) := by
  refine ⟨fun i hi => (hf.smooth i hi).coeff_mul (ha i hi),fun n => ?_⟩
  apply ((FamilyGrowth.of_bound hA (fun i hi t ht _ => hab i hi t ht)).mul (hf.bounds n)).congr
  intro i hi t ht x
  exact (iteratedDeriv_const_mul_field (n:=n) (x:=x) (a i t) (F i t)).symm

lemma PolynomialJetFamily.const_mul {ι : Type*} {P : ι → Prop} {T : Set ℝ}
    {F : ι → ℝ → ℝ → ℝ} (hf : PolynomialJetFamily P T F) (c : ℝ) :
    PolynomialJetFamily P T (fun i t x => c*F i t x) :=
  hf.coeff_mul (fun _ _ => continuousOn_const) (abs_nonneg c) (fun _ _ _ _ => le_rfl)

lemma PolynomialJetFamily.sub {ι : Type*} {P : ι → Prop} {T : Set ℝ} {F G : ι → ℝ → ℝ → ℝ}
    (hf : PolynomialJetFamily P T F) (hg : PolynomialJetFamily P T G) :
    PolynomialJetFamily P T (fun i t x => F i t x-G i t x) := by
  simpa only [neg_one_mul,sub_eq_add_neg] using hf.add (hg.const_mul (-1))

lemma PolynomialJetFamily.mul {ι : Type*} {P : ι → Prop} {T : Set ℝ} {F G : ι → ℝ → ℝ → ℝ}
    (hf : PolynomialJetFamily P T F) (hg : PolynomialJetFamily P T G) :
    PolynomialJetFamily P T (fun i t x => F i t x*G i t x) := by
  refine ⟨fun i hi => (hf.smooth i hi).mul (hg.smooth i hi),fun n => ?_⟩
  have hb : FamilyGrowth P T (fun i t x => ∑ k∈Finset.range (n+1),
      (n.choose k:ℝ)*iteratedDeriv k (F i t) x*iteratedDeriv (n-k) (G i t) x) := by
    apply FamilyGrowth.finset_sum
    intro k hk
    exact ((hf.bounds k).const_mul (n.choose k:ℝ)).mul (hg.bounds (n-k))
  apply hb.congr
  intro i hi t ht x
  exact (iteratedDeriv_fun_mul ((hf.smooth i hi).1 t ht |>.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))).contDiffAt
    ((hg.smooth i hi).1 t ht |>.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))).contDiffAt).symm

end Higher
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
namespace Parameter

def dd1 (F : ℝ → ℝ) (a b : ℝ) : ℝ := (F b-F a)/(b-a)
def dd2 (F : ℝ → ℝ) (a b c : ℝ) : ℝ := (dd1 F b c-dd1 F a b)/(c-a)
def dd3 (F : ℝ → ℝ) (a b c d : ℝ) : ℝ := (dd2 F b c d-dd2 F a b c)/(d-a)

lemma dd1_sub_slope (F : ℝ → ℝ) {a b c : ℝ}
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    dd1 F a b-dd1 F a c=(b-c)*dd2 F a b c := by
  simp only [dd2,dd1]
  field_simp [sub_ne_zero.mpr hab.symm,sub_ne_zero.mpr hac.symm,sub_ne_zero.mpr hbc.symm]
  ring

lemma dd2_sub_last (F : ℝ → ℝ) {a b c d : ℝ}
    (hab : a≠b) (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) (hcd : c≠d) :
    dd2 F a b c-dd2 F a b d=(c-d)*dd3 F a b c d := by
  simp only [dd3,dd2,dd1]
  field_simp [sub_ne_zero.mpr hab.symm,sub_ne_zero.mpr hac.symm,sub_ne_zero.mpr had.symm,
    sub_ne_zero.mpr hbc.symm,sub_ne_zero.mpr hbd.symm,sub_ne_zero.mpr hcd.symm]
  ring

lemma dd1_square (F : ℝ → ℝ) (a b : ℝ) :
    dd1 (fun x => (F x)^2) a b=(F a+F b)*dd1 F a b := by unfold dd1; ring

lemma dd2_square (F : ℝ → ℝ) {a b c : ℝ}
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    dd2 (fun x => (F x)^2) a b c=(F a+F c)*dd2 F a b c+dd1 F a b*dd1 F b c := by
  simp only [dd2,dd1]
  field_simp [sub_ne_zero.mpr hab.symm,sub_ne_zero.mpr hac.symm,sub_ne_zero.mpr hbc.symm]
  ring

lemma dd3_square (F : ℝ → ℝ) {a b c d : ℝ}
    (hab : a≠b) (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) (hcd : c≠d) :
    dd3 (fun x => (F x)^2) a b c d=(F a+F d)*dd3 F a b c d+
      dd1 F a b*dd2 F b c d+dd2 F a b c*dd1 F c d := by
  simp only [dd3,dd2,dd1]
  field_simp [sub_ne_zero.mpr hab.symm,sub_ne_zero.mpr hac.symm,sub_ne_zero.mpr had.symm,
    sub_ne_zero.mpr hbc.symm,sub_ne_zero.mpr hbd.symm,sub_ne_zero.mpr hcd.symm]
  ring

lemma dd1_affine_mul (F : ℝ → ℝ) (A B : ℝ) {a b : ℝ} (hab : a≠b) :
    dd1 (fun x => (A+x*B)*F x) a b=(A+a*B)*dd1 F a b+B*F b := by
  unfold dd1
  field_simp [sub_ne_zero.mpr hab.symm]
  ring

lemma dd2_affine_mul (F : ℝ → ℝ) (A B : ℝ) {a b c : ℝ}
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    dd2 (fun x => (A+x*B)*F x) a b c=(A+a*B)*dd2 F a b c+B*dd1 F b c := by
  simp only [dd2,dd1]
  field_simp [sub_ne_zero.mpr hab.symm,sub_ne_zero.mpr hac.symm,sub_ne_zero.mpr hbc.symm]
  ring

lemma dd3_affine_mul (F : ℝ → ℝ) (A B : ℝ) {a b c d : ℝ}
    (hab : a≠b) (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) (hcd : c≠d) :
    dd3 (fun x => (A+x*B)*F x) a b c d=(A+a*B)*dd3 F a b c d+B*dd2 F b c d := by
  simp only [dd3,dd2,dd1]
  field_simp [sub_ne_zero.mpr hab.symm,sub_ne_zero.mpr hac.symm,sub_ne_zero.mpr had.symm,
    sub_ne_zero.mpr hbc.symm,sub_ne_zero.mpr hbd.symm,sub_ne_zero.mpr hcd.symm]
  ring

end Parameter
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
namespace Parameter
open Higher

structure Nodes2 (I : Set ℝ) where
  a : ℝ
  b : ℝ
  ha : a∈I
  hb : b∈I
  hab : a≠b

structure Nodes3 (I : Set ℝ) extends Nodes2 I where
  c : ℝ
  hc : c∈I
  hac : a≠c
  hbc : b≠c

structure Nodes4 (I : Set ℝ) extends Nodes3 I where
  d : ℝ
  hd : d∈I
  had : a≠d
  hbd : b≠d
  hcd : c≠d

def Nodes3.bc {I : Set ℝ} (p : Nodes3 I) : Nodes2 I := ⟨p.b,p.c,p.hb,p.hc,p.hbc⟩
def Nodes4.bcd {I : Set ℝ} (p : Nodes4 I) : Nodes3 I := ⟨p.toNodes3.bc,p.d,p.hd,p.hbd,p.hcd⟩
def Nodes4.cd {I : Set ℝ} (p : Nodes4 I) : Nodes2 I := ⟨p.c,p.d,p.hc,p.hd,p.hcd⟩

def field1 (F : ℝ → ℝ → ℝ → ℝ) (a b t x : ℝ) : ℝ := dd1 (fun e => F e t x) a b
def field2 (F : ℝ → ℝ → ℝ → ℝ) (a b c t x : ℝ) : ℝ := dd2 (fun e => F e t x) a b c
def field3 (F : ℝ → ℝ → ℝ → ℝ) (a b c d t x : ℝ) : ℝ := dd3 (fun e => F e t x) a b c d

lemma divided_smooth {T : Set ℝ} {F G : ℝ → ℝ → ℝ}
    (hf : JointSpatialSmooth T F) (hg : JointSpatialSmooth T G) (c : ℝ) :
    JointSpatialSmooth T (fun t x => (G t x-F t x)/c) := by
  simpa only [div_eq_mul_inv,mul_comm] using (hg.sub hf).coeff_mul (a:=fun _ => c⁻¹) continuousOn_const

lemma divided_jet (n : ℕ) {F G : ℝ → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) (c x : ℝ) :
    iteratedDeriv n (fun y => (G y-F y)/c) x = (iteratedDeriv n G x-iteratedDeriv n F x)/c := by
  have hf' : ContDiff ℝ (n : WithTop ℕ∞) F := hf.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))
  have hg' : ContDiff ℝ (n : WithTop ℕ∞) G := hg.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))
  simp only [div_eq_mul_inv,mul_comm _ c⁻¹]
  rw [iteratedDeriv_const_mul_field,iteratedDeriv_fun_sub hg'.contDiffAt hf'.contDiffAt]

lemma field1_smooth {I T : Set ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : ∀ e∈I,JointSpatialSmooth T (F e)) (p : Nodes2 I) : JointSpatialSmooth T (field1 F p.a p.b) :=
  divided_smooth (hf p.a p.ha) (hf p.b p.hb) (p.b-p.a)

lemma field2_smooth {I T : Set ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : ∀ e∈I,JointSpatialSmooth T (F e)) (p : Nodes3 I) : JointSpatialSmooth T (field2 F p.a p.b p.c) :=
  divided_smooth (field1_smooth hf p.toNodes2) (field1_smooth hf p.bc) (p.c-p.a)

lemma field3_smooth {I T : Set ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : ∀ e∈I,JointSpatialSmooth T (F e)) (p : Nodes4 I) : JointSpatialSmooth T (field3 F p.a p.b p.c p.d) :=
  divided_smooth (field2_smooth hf p.toNodes3) (field2_smooth hf p.bcd) (p.d-p.a)

lemma field1_jet {I T : Set ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : ∀ e∈I,JointSpatialSmooth T (F e)) (p : Nodes2 I) (n : ℕ) {t : ℝ} (ht : t∈T) (x : ℝ) :
    iteratedDeriv n (field1 F p.a p.b t) x=dd1 (fun e => iteratedDeriv n (F e t) x) p.a p.b :=
  divided_jet n ((hf p.a p.ha).1 t ht) ((hf p.b p.hb).1 t ht) (p.b-p.a) x

lemma field2_jet {I T : Set ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : ∀ e∈I,JointSpatialSmooth T (F e)) (p : Nodes3 I) (n : ℕ) {t : ℝ} (ht : t∈T) (x : ℝ) :
    iteratedDeriv n (field2 F p.a p.b p.c t) x=dd2 (fun e => iteratedDeriv n (F e t) x) p.a p.b p.c := by
  change iteratedDeriv n (fun y => (field1 F p.b p.c t y-field1 F p.a p.b t y)/(p.c-p.a)) x=_
  have hh := divided_jet n ((field1_smooth hf p.toNodes2).1 t ht) ((field1_smooth hf p.bc).1 t ht) (p.c-p.a) x
  dsimp [Nodes3.bc] at hh
  rw [hh]
  have hb := field1_jet hf p.bc n ht x
  dsimp [Nodes3.bc] at hb
  rw [hb,field1_jet hf p.toNodes2 n ht]
  rfl

lemma field3_jet {I T : Set ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : ∀ e∈I,JointSpatialSmooth T (F e)) (p : Nodes4 I) (n : ℕ) {t : ℝ} (ht : t∈T) (x : ℝ) :
    iteratedDeriv n (field3 F p.a p.b p.c p.d t) x=dd3 (fun e => iteratedDeriv n (F e t) x) p.a p.b p.c p.d := by
  change iteratedDeriv n (fun y => (field2 F p.b p.c p.d t y-field2 F p.a p.b p.c t y)/(p.d-p.a)) x=_
  have hh := divided_jet n ((field2_smooth hf p.toNodes3).1 t ht) ((field2_smooth hf p.bcd).1 t ht) (p.d-p.a) x
  dsimp [Nodes4.bcd,Nodes3.bc] at hh
  rw [hh]
  have hb := field2_jet hf p.bcd n ht x
  dsimp [Nodes4.bcd,Nodes3.bc] at hb
  rw [hb,field2_jet hf p.toNodes3 n ht]
  rfl

lemma fixed_family {I T : Set ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : PolynomialJetFamily (fun e => e∈I) T F) {e : ℝ} (he : e∈I) :
    PolynomialJetFamily (fun _ : Unit => True) T (fun _ => F e) :=
  hf.comp (fun _ => e) (fun _ _ => he)

lemma field1_individual {I T : Set ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : PolynomialJetFamily (fun e => e∈I) T F) (p : Nodes2 I) :
    PolynomialJetFamily (fun _ : Unit => True) T (fun _ => field1 F p.a p.b) := by
  change PolynomialJetFamily (fun _ : Unit => True) T (fun _ t x => (F p.b t x-F p.a t x)/(p.b-p.a))
  have hh := ((fixed_family hf p.hb).sub (fixed_family hf p.ha)).const_mul ((p.b-p.a)⁻¹)
  simpa only [field1,dd1,div_eq_mul_inv,mul_comm (p.b-p.a)⁻¹] using hh

lemma field2_individual {I T : Set ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : PolynomialJetFamily (fun e => e∈I) T F) (p : Nodes3 I) :
    PolynomialJetFamily (fun _ : Unit => True) T (fun _ => field2 F p.a p.b p.c) := by
  change PolynomialJetFamily (fun _ : Unit => True) T (fun _ t x => (field1 F p.b p.c t x-field1 F p.a p.b t x)/(p.c-p.a))
  have hh := ((field1_individual hf p.bc).sub (field1_individual hf p.toNodes2)).const_mul ((p.c-p.a)⁻¹)
  simpa only [Nodes3.bc,field2,field1,dd2,div_eq_mul_inv,mul_comm (p.c-p.a)⁻¹] using hh

lemma field3_individual {I T : Set ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : PolynomialJetFamily (fun e => e∈I) T F) (p : Nodes4 I) :
    PolynomialJetFamily (fun _ : Unit => True) T (fun _ => field3 F p.a p.b p.c p.d) := by
  change PolynomialJetFamily (fun _ : Unit => True) T (fun _ t x => (field2 F p.b p.c p.d t x-field2 F p.a p.b p.c t x)/(p.d-p.a))
  have hh := ((field2_individual hf p.bcd).sub (field2_individual hf p.toNodes3)).const_mul ((p.d-p.a)⁻¹)
  simpa only [Nodes4.bcd,Nodes3.bc,field3,field2,dd3,div_eq_mul_inv,mul_comm (p.d-p.a)⁻¹] using hh

end Parameter
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
lemma rowSmooth_perturbation {Q : ℝ} {q η : ℝ → ℝ}
    (hq : RowSmoothProfile Q q)
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η) (hη0 : η 0=0) (hη1 : η 1=0) :
    ∃ r : ℝ, 0<r ∧ ∀ ε, |ε|<r → RowSmoothProfile Q (fun s => q s+ε*η s) := by
  have hqc : Continuous (deriv q) := (contDiff_infty_iff_deriv.mp hq.1).2.continuous
  have hηc : Continuous (deriv η) := (contDiff_infty_iff_deriv.mp hη).2.continuous
  obtain ⟨c,hc,hcmin⟩ := isCompact_Icc.exists_forall_le' hqc.continuousOn hq.2.2.2
  obtain ⟨s,hs,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by norm_num : (0:ℝ)≤1)) hηc.abs.continuousOn
  let M := |deriv η s|+1
  have hM : 0<M := by dsimp [M]; positivity
  refine ⟨c/(2*M),div_pos hc (by positivity),fun ε hε => ?_⟩
  refine ⟨hq.1.add (contDiff_const.mul hη),?_,?_,?_⟩
  · simp [hq.2.1,hη0]
  · simp [hq.2.2.1,hη1]
  · intro t ht
    have hd := ((hq.1.differentiable (by simp) t).hasDerivAt.add
      ((hη.differentiable (by simp) t).hasDerivAt.const_mul ε)).deriv
    change 0 < deriv (q + fun y => ε*η y) t
    rw [hd]
    have hle : |deriv η t| ≤ M := (hmax ht).trans (by dsimp [M]; linarith)
    have hmul : |ε| *M<c/2 := by
      have hh := (lt_div_iff₀ (show 0<2*M by positivity)).mp hε
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hle (abs_nonneg ε)
    have hb : |ε*deriv η t|<c/2 := by rw [abs_mul]; exact hh.trans_lt hmul
    linarith [neg_abs_le (ε*deriv η t),hcmin t ht]

 

lemma row_rank_neighborhood_existence {A B C κ Q : ℝ} {u q η : ℝ → ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q) (hq : RowSmoothProfile Q q)
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η) (hη0 : η 0=0) (hη1 : η 1=0) :
    ∃ r : ℝ, 0<r ∧ ∃ f : ℝ → ℝ → ℝ → ℝ,
      ∀ ε, |ε|<r → RowClassicalRankSolution u (fun s => q s+ε*η s) (f ε) := by
  classical
  obtain ⟨r,hr,hrq⟩ := rowSmooth_perturbation hq hη hη0 hη1
  have hex : ∀ ε, ∃ f, |ε|<r → RowClassicalRankSolution u (fun s => q s+ε*η s) f := by
    intro ε
    by_cases he : |ε|<r
    · obtain ⟨f,hf,_⟩ := row_rank_existence_unique hQ hu (hrq ε he)
      exact ⟨f,fun _ => hf⟩
    · exact ⟨fun _ _ => 0,fun hh => (he hh).elim⟩
  choose f hf using hex
  exact ⟨r,hr,f,hf⟩
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming

lemma row_variance_jet_uniform {A B C κ Q : ℝ} {u : ℝ → ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q) (k : ℕ) (hk : 2≤k) :
    ∃ H : ℝ,0≤H ∧ ∀ m : ℝ → ℝ,ContinuousOn m (Icc 0 Q) →
      (∀ t∈Icc 0 Q,0 ≤ m t ∧ m t≤1) → ∀ F : ℝ → ℝ → ℝ,
      RowClassicalVarianceSolution Q u m F →
      ∀ t∈Icc 0 Q,∀ x,|iteratedDeriv k (F t) x|≤H := by
  obtain ⟨H,hH,hbound⟩ := Higher.gaussianRowComposition_all_jets hQ hu k hk
  refine ⟨H,hH,fun m hm hmb F hF => ?_⟩
  obtain ⟨L,hL,hh⟩ := row_variance_existence A B C κ Q hQ hu.2.1 hu.2.2.1 hu.2.2.2.1 hu.2.2.2.2.1
  obtain ⟨G,hG,_,huniq,hconv⟩ := hh u hu m hm hmb
  obtain ⟨rs,hrs,hT,hrm⟩ := exists_gaussian_grid_approximation hQ hm hmb
  have hc : CylinderConvergence (fun n => gaussianStepPath (rs n) u) F (Icc 0 Q) := by
    intro R hR
    exact (hconv rs hrs hT hrm R hR).congr_right (fun p hp => huniq F hF p.1 hp.1 p.2)
  have hvalid (n : ℕ) (t : ℝ) (ht : t∈Icc 0 Q) :
      (∀ r∈gaussianStepRemainder (rs n) t,0≤r.1 ∧ r.1≤1 ∧ 0≤r.2) ∧
      gaussianStepTime (gaussianStepRemainder (rs n) t)≤Q := by
    obtain ⟨hv,he⟩ := gaussianStepRemainder_valid (hrs n) ht.1
    refine ⟨hv,?_⟩
    rw [he,hT,max_eq_left (by linarith [ht.2])]
    linarith [ht.1]
  have hs (n : ℕ) (t : ℝ) (ht : t∈Icc 0 Q) :
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gaussianStepPath (rs n) u t) :=
    (Higher.gaussianRowComposition_smoothPolynomial hQ hu _ (hvalid n t ht).1 (hvalid n t ht).2).smooth
  have hb : ∀ l : ℕ,2≤l → ∃ J : ℝ,0≤J ∧ ∀ n t,t∈Icc 0 Q → ∀ x,
      |iteratedDeriv l (gaussianStepPath (rs n) u t) x|≤J := by
    intro l hl
    obtain ⟨J,hJ,hh⟩ := Higher.gaussianRowComposition_all_jets hQ hu l hl
    exact ⟨J,hJ,fun n t ht x => hh _ (hvalid n t ht).1 (hvalid n t ht).2 x⟩
  have hj := (hc.all_jets hs hb).1 k
  intro t ht x
  exact le_of_tendsto (hj.tendsto_at ht x).abs (Eventually.of_forall (fun n =>
    hbound _ (hvalid n t ht).1 (hvalid n t ht).2 x))

lemma row_rank_smooth {A B C κ Q : ℝ} {u q : ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q) (hq : RowSmoothProfile Q q)
    (hf : RowClassicalRankSolution u q f) : Higher.JointSpatialSmooth (Icc 0 1) f := by
  obtain ⟨m,hm,hmb,hinv,hleft⟩ := rowSmooth_inverse hq
  have hF := rowRank_to_variance hq hm hmb hinv hleft hf
  have hh := row_variance_all_jets hQ hu hm hmb hF
  have he (s : ℝ) (hs : s∈Icc (0:ℝ) 1) : m (q s)=s := hleft s hs
  refine ⟨fun s hs => ?_,fun n => ?_⟩
  · simpa only [he s hs] using hh.1 (q s) (hq.mapsTo hs)
  · have hc := (hh.2.1 n).comp
      (((hq.1.continuous.comp continuous_fst).prodMk continuous_snd).continuousOn)
      (fun (p : ℝ × ℝ) (hp : p∈Icc 0 1 ×ˢ univ) => (show (q p.1,p.2)∈Icc 0 Q ×ˢ univ from ⟨hq.mapsTo hp.1,mem_univ _⟩))
    apply hc.congr
    intro p hp
    change iteratedDeriv n (f p.1) p.2=iteratedDeriv n (f (m (q p.1))) p.2
    rw [he p.1 hp.1]

lemma row_rank_jets_time {A B C κ Q : ℝ} {u q : ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q) (hq : RowSmoothProfile Q q)
    (hf : RowClassicalRankSolution u q f) :
    ∀ n : ℕ,∀ t∈Ico (0:ℝ) 1,∀ x,HasDerivWithinAt (fun s => iteratedDeriv n (f s) x)
      (iteratedDeriv n (fun y => -(deriv q t)/2*(iteratedDeriv 2 (f t) y+t*(iteratedDeriv 1 (f t) y)^2)) x)
      (Ici t) t := by
  have hs := row_rank_smooth hQ hu hq hf
  have ha : ContinuousOn (fun t => deriv q t/2) (Icc (0:ℝ) 1) :=
    ((contDiff_infty_iff_deriv.mp hq.1).2.continuous.div_const 2).continuousOn
  have hg := hs.row_rhs ha continuousOn_id
  apply evolution_all_jets (by norm_num : (0:ℝ)<1) hf.1 (by simpa only [neg_div,id_eq] using hg.2)
    hs.1 (by simpa only [neg_div,id_eq] using hg.1)
  intro t ht x
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hf.2.2.2.2.1 t ht x

lemma row_rank_uniform_bounds {A B C κ Q : ℝ} {u : ℝ → ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q) :
    ∃ L : ℝ,0≤L ∧ ∃ H : ℕ → ℝ,(∀ n,0≤H n) ∧
      ∀ q : ℝ → ℝ,RowSmoothProfile Q q → ∀ f : ℝ → ℝ → ℝ,
      RowClassicalRankSolution u q f →
      (∀ t∈Icc (0:ℝ) 1,∀ x,|f t x|≤L*(1+x^2) ∧ |deriv (f t) x|≤L*(1+|x|)) ∧
      (∀ n : ℕ,2≤n → ∀ t∈Icc (0:ℝ) 1,∀ x,|iteratedDeriv n (f t) x|≤H n) := by
  classical
  obtain ⟨L,hL,hsolve⟩ := row_variance_existence A B C κ Q hQ hu.2.1 hu.2.2.1 hu.2.2.2.1 hu.2.2.2.2.1
  have hh : ∀ n : ℕ,∃ H : ℝ,0≤H ∧ ∀ m,ContinuousOn m (Icc 0 Q) →
      (∀ t∈Icc 0 Q,0 ≤ m t ∧ m t≤1) → ∀ F,RowClassicalVarianceSolution Q u m F →
      2≤n → ∀ t∈Icc 0 Q,∀ x,|iteratedDeriv n (F t) x|≤H := by
    intro n
    by_cases hn : 2≤n
    · obtain ⟨H,hH,hh⟩ := row_variance_jet_uniform hQ hu n hn
      exact ⟨H,hH,fun m hm hmb F hF _ => hh m hm hmb F hF⟩
    · exact ⟨0,le_refl _,fun _ _ _ _ _ h => (hn h).elim⟩
  choose H hH hHbound using hh
  let D := L+A*(1+Q)+|B|
  have hA : 0≤A := hu.2.1
  have hD : 0≤D := by dsimp [D]; positivity
  refine ⟨D,hD,H,hH,fun q hq f hf => ?_⟩
  obtain ⟨m,hm,hmb,hinv,hleft⟩ := rowSmooth_inverse hq
  have hF := rowRank_to_variance hq hm hmb hinv hleft hf
  obtain ⟨G,hG,hbd,huniq,_⟩ := hsolve u hu m hm hmb
  have he (t : ℝ) (htt : t∈Icc 0 Q) : G t=f (m t) := funext (fun x => huniq _ hF t htt x)
  have hb (t : ℝ) (htt : t∈Icc (0:ℝ) 1) (x : ℝ) := hbd (q t) (hq.mapsTo htt) x
  constructor
  · intro t htt x
    have hb' := hb t htt x
    rw [he (q t) (hq.mapsTo htt),hleft t htt] at hb'
    have hq0 := (hq.mapsTo htt).1
    have hval : |f t x| ≤ (A*(1+Q)+|B|)*(1+x^2) := by
      rw [abs_le]
      constructor
      · nlinarith [hb'.1,abs_nonneg B,mul_nonneg hA (sq_nonneg x),mul_nonneg (abs_nonneg B) (sq_nonneg x),mul_nonneg hA hq0,mul_nonneg (mul_nonneg hA hQ.le) (sq_nonneg x)]
      · nlinarith [hb'.2.1,le_abs_self B,abs_nonneg B,mul_nonneg (abs_nonneg B) (sq_nonneg x),mul_nonneg hA (sq_nonneg x),mul_nonneg (mul_nonneg hA hQ.le) (sq_nonneg x),mul_nonneg hA hQ.le]
    refine ⟨hval.trans (mul_le_mul_of_nonneg_right (by dsimp [D]; linarith) (by positivity)),?_⟩
    exact hb'.2.2.1.trans (mul_le_mul_of_nonneg_right (by dsimp [D]; linarith [mul_nonneg hA (show 0≤1+Q by linarith),abs_nonneg B]) (by positivity))
  · intro n hn t htt x
    simpa only [hleft t htt] using hHbound n m hm hmb _ hF hn (q t) (hq.mapsTo htt) x
end MicroscopicJamming

end

end OAI
