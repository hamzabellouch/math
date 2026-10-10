import Mathlib
import OAI.Probability.JammingConcavity.PolynomialComparison

namespace OAI

/-! Cylinder Secants. -/

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
open Set Filter
open scoped Topology

namespace MicroscopicJamming

 
lemma deriv_difference_secant {f g : ℝ → ℝ} {K E x h : ℝ}
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f))
    (hg : Differentiable ℝ g) (hg' : Differentiable ℝ (deriv g))
    (hK : 0 ≤ K) (hbf : ∀ z, |deriv (deriv f) z| ≤ K)
    (hbg : ∀ z, |deriv (deriv g) z| ≤ K) (hh : 0 < h)
    (he0 : |f x-g x| ≤ E) (he1 : |f (x+h)-g (x+h)| ≤ E) :
    |deriv f x-deriv g x| ≤ 2*K*h+2*E/h := by
  have hfsec := deriv_secant_error hf hf' hK hbf (x:=x) hh
  have hgsec := deriv_secant_error hg hg' hK hbg (x:=x) hh
  have hsec : |(f (x+h)-f x)/h-(g (x+h)-g x)/h| ≤ 2*E/h := by
    rw [← sub_div,abs_div,abs_of_pos hh]
    apply div_le_div_of_nonneg_right _ hh.le
    have he : (f (x+h)-f x)-(g (x+h)-g x)=(f (x+h)-g (x+h))-(f x-g x) := by ring
    rw [he]
    exact (abs_sub _ _).trans (by linarith)
  have ht1 := abs_sub_le (deriv f x) ((f (x+h)-f x)/h) (deriv g x)
  have ht2 := abs_sub_le ((f (x+h)-f x)/h) ((g (x+h)-g x)/h) (deriv g x)
  rw [abs_sub_comm (deriv g x)] at hgsec
  linarith

 
def CylinderCauchy (f : ℕ → ℝ → ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ R : ℝ, 0 < R → UniformCauchySeqOn (fun n (p : ℝ × ℝ) => f n p.1 p.2)
    atTop (S ×ˢ Icc (-R) R)

lemma CylinderCauchy.deriv {f : ℕ → ℝ → ℝ → ℝ} {S : Set ℝ} {K : ℝ}
    (hc : CylinderCauchy f S) (hK : 0 ≤ K)
    (hd : ∀ n t, t ∈ S → Differentiable ℝ (f n t) ∧ Differentiable ℝ (deriv (f n t)))
    (hb : ∀ n t, t ∈ S → ∀ x, |deriv (deriv (f n t)) x| ≤ K) :
    CylinderCauchy (fun n t => deriv (f n t)) S := by
  intro R hR
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  let h := min 1 (ε/(8*(K+1)))
  have hh : 0 < h := lt_min zero_lt_one (div_pos hε (by positivity))
  have hh1 : h ≤ 1 := min_le_left _ _
  have hhK : 8*(K+1)*h ≤ ε := by
    have hd := min_le_right 1 (ε/(8*(K+1)))
    simpa only [h,mul_comm] using (le_div_iff₀ (by positivity : 0 < 8*(K+1))).mp hd
  obtain ⟨N,hN⟩ := (Metric.uniformCauchySeqOn_iff.mp (hc (R+1) (by linarith)))
    (ε*h/8) (by positivity)
  refine ⟨N,fun n hn k hk p hp => ?_⟩
  have hx : p.2 ∈ Icc (-(R+1)) (R+1) := by constructor <;> linarith [hp.2.1,hp.2.2]
  have hxh : p.2+h ∈ Icc (-(R+1)) (R+1) := by constructor <;> linarith [hp.2.1,hp.2.2]
  have he0 : |f n p.1 p.2-f k p.1 p.2| ≤ ε*h/8 :=
    (hN n hn k hk (p.1,p.2) ⟨hp.1,hx⟩).le
  have he1 : |f n p.1 (p.2+h)-f k p.1 (p.2+h)| ≤ ε*h/8 :=
    (hN n hn k hk (p.1,p.2+h) ⟨hp.1,hxh⟩).le
  have he := deriv_difference_secant (hd n p.1 hp.1).1 (hd n p.1 hp.1).2
    (hd k p.1 hp.1).1 (hd k p.1 hp.1).2 hK (hb n p.1 hp.1) (hb k p.1 hp.1) hh he0 he1
  have hdv : 2*(ε*h/8)/h=ε/4 := by field_simp; ring
  rw [hdv] at he
  rw [Real.dist_eq]
  nlinarith

lemma CylinderCauchy.exists_limit {f : ℕ → ℝ → ℝ → ℝ} {S : Set ℝ}
    (hc : CylinderCauchy f S) : ∃ F : ℝ → ℝ → ℝ,
    ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n (p : ℝ × ℝ) => f n p.1 p.2)
      (fun p => F p.1 p.2) atTop (S ×ˢ Icc (-R) R) := by
  classical
  have hex (t x : ℝ) (ht : t ∈ S) : ∃ y : ℝ, Tendsto (fun n => f n t x) atTop (𝓝 y) := by
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.uniformCauchySeqOn_iff.mp (hc (|x|+1) (by positivity)) ε hε
    refine ⟨N,fun n hn k hk => hN n hn k hk (t,x) ⟨ht,?_,?_⟩⟩
    · linarith [neg_abs_le x]
    · linarith [le_abs_self x]
  let F : ℝ → ℝ → ℝ := fun t x => if ht : t ∈ S then (hex t x ht).choose else 0
  refine ⟨F,fun R hR => (hc R hR).tendstoUniformlyOn_of_tendsto ?_⟩
  intro p hp
  simpa only [F,dite_eq_left hp.1] using (hex p.1 p.2 hp.1).choose_spec

lemma continuousOn_spatial_deriv {f : ℝ → ℝ → ℝ} {S : Set ℝ} {K : ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (S ×ˢ univ))
    (hd : ∀ t ∈ S, Differentiable ℝ (f t) ∧ Differentiable ℝ (deriv (f t)))
    (hK : 0 ≤ K) (hb : ∀ t ∈ S, ∀ x, |deriv (deriv (f t)) x| ≤ K) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (f p.1) p.2) (S ×ˢ univ) := by
  let h : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hh (n : ℕ) : 0 < h n := by dsimp [h]; positivity
  have hlim : Tendsto h atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hsec : TendstoUniformlyOn (fun n (p : ℝ × ℝ) =>
      (f p.1 (p.2+h n)-f p.1 p.2)/h n)
      (fun p => deriv (f p.1) p.2) atTop (S ×ˢ univ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have he : ∀ᶠ n in atTop, K*h n < ε := by
      have hl : Tendsto (fun n => K*h n) atTop (𝓝 (K*0)) := tendsto_const_nhds.mul hlim
      exact hl.eventually (gt_mem_nhds (by simpa using hε))
    filter_upwards [he] with n hn p hp
    rw [Real.dist_eq]
    exact (deriv_secant_error (hd p.1 hp.1).1 (hd p.1 hp.1).2 hK (hb p.1 hp.1) (hh n)).trans_lt hn
  apply hsec.continuousOn
  apply Filter.Eventually.frequently
  apply Eventually.of_forall
  intro n
  have hmap : Continuous (fun p : ℝ × ℝ => (p.1,p.2+h n)) :=
    continuous_fst.prodMk (continuous_snd.add continuous_const)
  exact ((hc.comp hmap.continuousOn (fun p hp => ⟨hp.1,mem_univ _⟩)).sub hc).div_const _

lemma cylinder_limit_continuous {S : Set ℝ} {f : ℕ → ℝ → ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    (hf : ∀ n, ContinuousOn (fun p : ℝ × ℝ => f n p.1 p.2) (S ×ˢ univ))
    (hlim : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n (p : ℝ × ℝ) => f n p.1 p.2)
      (fun p => F p.1 p.2) atTop (S ×ˢ Icc (-R) R)) :
    ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (S ×ˢ univ) := by
  intro p hp
  let R := |p.2|+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hx : p.2 ∈ Ioo (-R) R := by
    dsimp [R]; constructor <;> linarith [neg_abs_le p.2,le_abs_self p.2]
  have hcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (S ×ˢ Icc (-R) R) :=
    (hlim R hR).continuousOn (Eventually.of_forall (fun n =>
      (hf n).mono (prod_mono_right (subset_univ _)))).frequently
  have hct := hcont p ⟨hp.1,hx.1.le,hx.2.le⟩
  apply hct.mono_of_mem_nhdsWithin
  have hn : (fun q : ℝ × ℝ => q.2) ⁻¹' Icc (-R) R ∈ 𝓝 p :=
    continuous_snd.continuousAt.preimage_mem_nhds (Icc_mem_nhds hx.1 hx.2)
  filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds hn] with q hq hqx
  exact ⟨hq.1,hqx⟩

end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming

def CylinderConvergence (f : ℕ → ℝ → ℝ → ℝ) (F : ℝ → ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n (p : ℝ × ℝ) => f n p.1 p.2)
    (fun p => F p.1 p.2) atTop (S ×ˢ Icc (-R) R)

lemma CylinderConvergence.tendsto_at {f : ℕ → ℝ → ℝ → ℝ} {F : ℝ → ℝ → ℝ} {S : Set ℝ}
    (hf : CylinderConvergence f F S) {t : ℝ} (ht : t ∈ S) (x : ℝ) :
    Tendsto (fun n => f n t x) atTop (𝓝 (F t x)) := by
  apply (hf (|x|+1) (by positivity)).tendsto_at (x := (t,x))
  exact ⟨ht,by linarith [neg_abs_le x],by linarith [le_abs_self x]⟩

lemma cylinder_limit_hasDerivAt {f : ℕ → ℝ → ℝ → ℝ} {F G : ℝ → ℝ → ℝ} {S : Set ℝ}
    (hv : CylinderConvergence f F S)
    (hg : CylinderConvergence (fun n t => deriv (f n t)) G S)
    (hd : ∀ n t, t ∈ S → Differentiable ℝ (f n t)) :
    ∀ t ∈ S, ∀ x, HasDerivAt (F t) (G t x) x := by
  intro t ht x
  let R := |x|+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hx : x ∈ Ioo (-R) R := by
    dsimp [R]; constructor <;> linarith [neg_abs_le x,le_abs_self x]
  have hgd : TendstoUniformlyOn (fun n => deriv (f n t)) (G t) atTop (Ioo (-R) R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hg R hR) ε hε] with n hn y hy
    exact hn (t,y) ⟨ht,hy.1.le,hy.2.le⟩
  exact hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hgd
    (Eventually.of_forall (fun n y _ => (hd n t ht y).hasDerivAt))
    (fun y _ => hv.tendsto_at ht y) hx

 

lemma exists_cylinder_c2_limit {f : ℕ → ℝ → ℝ → ℝ} {S : Set ℝ} {K H : ℝ}
    (hc : CylinderCauchy f S) (hf : ∀ n, ContinuousOn (fun p : ℝ × ℝ => f n p.1 p.2) (S ×ˢ univ))
    (hK : 0 ≤ K) (hH : 0 ≤ H)
    (hd : ∀ n t, t ∈ S → Differentiable ℝ (f n t) ∧
      Differentiable ℝ (deriv (f n t)) ∧ Differentiable ℝ (deriv (deriv (f n t))))
    (hb : ∀ n t, t ∈ S → ∀ x, |deriv (deriv (f n t)) x| ≤ K)
    (hb3 : ∀ n t, t ∈ S → ∀ x, |deriv (deriv (deriv (f n t))) x| ≤ H) :
    ∃ F : ℝ → ℝ → ℝ,
      ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (S ×ˢ univ) ∧
      ContinuousOn (fun p : ℝ × ℝ => deriv (F p.1) p.2) (S ×ˢ univ) ∧
      ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (F p.1)) p.2) (S ×ˢ univ) ∧
      (∀ t ∈ S, Differentiable ℝ (F t) ∧ Differentiable ℝ (deriv (F t))) ∧
      CylinderConvergence f F S ∧
      CylinderConvergence (fun n t => deriv (f n t)) (fun t => deriv (F t)) S ∧
      CylinderConvergence (fun n t => deriv (deriv (f n t))) (fun t => deriv (deriv (F t))) S := by
  have hc1 := hc.deriv hK (fun n t ht => ⟨(hd n t ht).1,(hd n t ht).2.1⟩) hb
  have hc2 := hc1.deriv hH (fun n t ht => (hd n t ht).2) hb3
  obtain ⟨F,hF⟩ := hc.exists_limit
  obtain ⟨G,hG⟩ := hc1.exists_limit
  obtain ⟨J,hJ⟩ := hc2.exists_limit
  have hdF := cylinder_limit_hasDerivAt hF hG (fun n t ht => (hd n t ht).1)
  have hdG := cylinder_limit_hasDerivAt (f := fun n t => deriv (f n t)) hG hJ (fun n t ht => (hd n t ht).2.1)
  have heF (t : ℝ) (ht : t ∈ S) : deriv (F t)=G t := funext (fun x => (hdF t ht x).deriv)
  have heG (t : ℝ) (ht : t ∈ S) : deriv (G t)=J t := funext (fun x => (hdG t ht x).deriv)
  have heJ (t : ℝ) (ht : t ∈ S) : deriv (deriv (F t))=J t := by rw [heF t ht,heG t ht]
  have hG' : CylinderConvergence (fun n t => deriv (f n t)) (fun t => deriv (F t)) S :=
    fun R hR => (hG R hR).congr_right (fun p hp => congrFun (heF p.1 hp.1).symm p.2)
  have hJ' : CylinderConvergence (fun n t => deriv (deriv (f n t))) (fun t => deriv (deriv (F t))) S :=
    fun R hR => (hJ R hR).congr_right (fun p hp => congrFun (heJ p.1 hp.1).symm p.2)
  have hfc1 (n : ℕ) : ContinuousOn (fun p : ℝ × ℝ => deriv (f n p.1) p.2) (S ×ˢ univ) :=
    continuousOn_spatial_deriv (hf n) (fun t ht => ⟨(hd n t ht).1,(hd n t ht).2.1⟩) hK (hb n)
  have hfc2 (n : ℕ) : ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (f n p.1)) p.2) (S ×ˢ univ) :=
    continuousOn_spatial_deriv (hfc1 n) (fun t ht => (hd n t ht).2) hH (hb3 n)
  refine ⟨F,cylinder_limit_continuous hf hF,cylinder_limit_continuous (f := fun n t => deriv (f n t)) (F := fun t => deriv (F t)) hfc1 hG',
    cylinder_limit_continuous (f := fun n t => deriv (deriv (f n t))) (F := fun t => deriv (deriv (F t))) hfc2 hJ',?_,hF,hG',hJ'⟩
  intro t ht
  refine ⟨fun x => (hdF t ht x).differentiableAt,?_⟩
  rw [heF t ht]
  exact fun x => (hdG t ht x).differentiableAt
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming

lemma gaussian_step_cylinder_cauchy {u m : ℝ → ℝ} {A B C κ Q : ℝ}
    (hQ : 0 < Q) (hu : RowAnalyticTerminal u A B C κ Q)
    {rs : ℕ → List (ℝ × ℝ)}
    (hrs : ∀ n, ∀ r ∈ rs n, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (hT : ∀ n, gaussianStepTime (rs n)=Q)
    (hm : TendstoUniformlyOn (fun n => gaussianStepCoefficient (rs n)) m atTop (Icc 0 Q)) :
    CylinderCauchy (fun n => gaussianStepPath (rs n) u) (Icc 0 Q) := by
  obtain ⟨L,hL,hstab⟩ := gaussian_step_stability A B C κ Q hQ hu.2.1 hu.2.2.1 hu.2.2.2.1 hu.2.2.2.2.1
  intro R hR
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  let M := L*(1+R^2)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let δ := ε/(M+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : δ*(M+1)=ε := div_mul_cancel₀ ε (by positivity)
  obtain ⟨N,hN⟩ := Metric.uniformCauchySeqOn_iff.mp hm.uniformCauchySeqOn δ hδ
  refine ⟨N,fun n hn k hk p hp => ?_⟩
  have hclose (t : ℝ) (ht : t ∈ Icc 0 Q) :
      |gaussianStepCoefficient (rs n) t-gaussianStepCoefficient (rs k) t| ≤ δ := (hN n hn k hk t ht).le
  have hh := hstab u hu (rs n) (rs k) (hrs n) (hrs k) (hT n) (hT k) δ hδ.le hclose p.1 hp.1 p.2
  have hx : p.2^2 ≤ R^2 := by
    have hxabs : |p.2| ≤ R := abs_le.mpr hp.2
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg p.2) hR.le).mpr hxabs
  have hbig : δ*L*(1+p.2^2) ≤ δ*M := by
    dsimp [M]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hδ.le hL)
  rw [Real.dist_eq]
  exact (hh.trans hbig).trans_lt (by nlinarith)

lemma gaussian_step_c2_limit {u m : ℝ → ℝ} {A B C κ Q : ℝ}
    (hQ : 0 < Q) (hu : RowAnalyticTerminal u A B C κ Q)
    {rs : ℕ → List (ℝ × ℝ)}
    (hrs : ∀ n, ∀ r ∈ rs n, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (hT : ∀ n, gaussianStepTime (rs n)=Q)
    (hm : TendstoUniformlyOn (fun n => gaussianStepCoefficient (rs n)) m atTop (Icc 0 Q)) :
    ∃ F : ℝ → ℝ → ℝ,
      ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc 0 Q ×ˢ univ) ∧
      ContinuousOn (fun p : ℝ × ℝ => deriv (F p.1) p.2) (Icc 0 Q ×ˢ univ) ∧
      ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (F p.1)) p.2) (Icc 0 Q ×ˢ univ) ∧
      (∀ t ∈ Icc 0 Q, Differentiable ℝ (F t) ∧ Differentiable ℝ (deriv (F t))) ∧
      CylinderConvergence (fun n => gaussianStepPath (rs n) u) F (Icc 0 Q) ∧
      CylinderConvergence (fun n t => deriv (gaussianStepPath (rs n) u t)) (fun t => deriv (F t)) (Icc 0 Q) ∧
      CylinderConvergence (fun n t => deriv (deriv (gaussianStepPath (rs n) u t)))
        (fun t => deriv (deriv (F t))) (Icc 0 Q) := by
  obtain ⟨D,L,hD,hL,hpath⟩ := gaussian_step_path A B C κ Q hQ hu.2.1 hu.2.2.1 hu.2.2.2.1 hu.2.2.2.2.1
  obtain ⟨H,hH,hthird⟩ := gaussian_step_third u A B C κ Q hQ hu
  let K := C+κ/(1-κ*Q)
  have hden : 0 < 1-κ*Q := by linarith [hu.2.2.2.2.1]
  have hK : 0 ≤ K := add_nonneg hu.2.2.1 (div_nonneg hu.2.2.2.1 hden.le)
  have hspace (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 Q) :=
    (hpath u hu (rs n) (hrs n) (hT n).le).2.2.2 t ht.1 (by rw [hT]; exact ht.2)
  have h3 (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 Q) :=
    hthird (rs n) (hrs n) (hT n).le t ht.1 (by rw [hT]; exact ht.2)
  apply exists_cylinder_c2_limit (gaussian_step_cylinder_cauchy hQ hu hrs hT hm) _ hK hH
    (fun n t ht => ⟨(hspace n t ht).1,(hspace n t ht).2.1,(h3 n t ht).1⟩) _
    (fun n t ht => (h3 n t ht).2)
  · intro n
    exact gaussianStepPath_jointly_continuous hD hL (hT n)
      (hpath u hu (rs n) (hrs n) (hT n).le).2.2.1
      (fun t ht htT => ⟨(hspace n t ⟨ht,by rwa [hT] at htT⟩).1,
        fun x => ((hspace n t ⟨ht,by rwa [hT] at htT⟩).2.2 x).1⟩)
  · intro n t ht x
    have hh := ((hspace n t ht).2.2 x).2
    rw [hT n] at hh
    have hupper : κ/(1-κ*(Q-t)) ≤ κ/(1-κ*Q) :=
      div_le_div_of_nonneg_left hu.2.2.2.1 hden (by nlinarith [mul_nonneg hu.2.2.2.1 ht.1])
    rw [abs_le]
    dsimp [K]
    constructor <;> linarith [div_nonneg hu.2.2.2.1 hden.le,hu.2.2.1,hh.1,hh.2]
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
lemma gaussianStepRightCoefficient_close_continuous {rs : List (ℝ × ℝ)} {m : ℝ → ℝ} {Q δ t : ℝ}
    (hm : ContinuousOn m (Icc 0 Q))
    (hb : ∀ s ∈ Icc 0 Q, |gaussianStepCoefficient rs s-m s| ≤ δ) (ht : t ∈ Ico 0 Q) :
    |gaussianStepRightCoefficient rs t-m t| ≤ δ := by
  obtain ⟨r,hr,htrace⟩ := gaussianStepRightCoefficient_trace rs t
  have hmt : Tendsto m (𝓝[>] t) (𝓝 (m t)) :=
    (hm t ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT_of_mem ht)
  have hl := (tendsto_const_nhds (x:=gaussianStepRightCoefficient rs t)).sub hmt |>.abs
  apply le_of_tendsto hl
  have hupper : ∀ᶠ s : ℝ in 𝓝[>] t, s < t+r :=
    (eventually_lt_nhds (by linarith : t<t+r)).filter_mono nhdsWithin_le_nhds
  filter_upwards [Icc_mem_nhdsGT_of_mem ht,self_mem_nhdsWithin,hupper] with s hs hst hsr
  simpa only [htrace s ⟨hst,hsr⟩] using hb s hs

lemma gaussianStepRightCoefficient_tendsto {rs : ℕ → List (ℝ × ℝ)} {m : ℝ → ℝ} {Q : ℝ}
    (hm : ContinuousOn m (Icc 0 Q))
    (hc : TendstoUniformlyOn (fun n => gaussianStepCoefficient (rs n)) m atTop (Icc 0 Q)) :
    TendstoUniformlyOn (fun n => gaussianStepRightCoefficient (rs n)) m atTop (Ico 0 Q) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hc (ε/2) (half_pos hε)] with n hn t ht
  rw [Real.dist_eq,abs_sub_comm]
  apply (gaussianStepRightCoefficient_close_continuous hm (rs:=rs n) (δ:=ε/2) ?_ ht).trans_lt (half_lt_self hε)
  intro s hs
  have hh := (hn s hs).le
  simpa only [Real.dist_eq,abs_sub_comm] using hh
end MicroscopicJamming

 
open Set Filter MeasureTheory
open scoped Topology

namespace MicroscopicJamming

 

lemma hasDerivAt_of_uniform_right_derivatives {a b : ℝ} (hab : a < b)
    {f g : ℕ → ℝ → ℝ} {F G : ℝ → ℝ}
    (hc : ∀ n, ContinuousOn (f n) (Icc a b))
    (hd : ∀ n t, t ∈ Ico a b → HasDerivWithinAt (f n) (g n t) (Ici t) t)
    (hv : ∀ t ∈ Icc a b, Tendsto (fun n => f n t) atTop (𝓝 (F t)))
    (hg : TendstoUniformlyOn g G atTop (Ico a b))
    (hG : ContinuousOn G (Icc a b)) :
    ∀ t ∈ Ioo a b, HasDerivAt F (G t) t := by
  let E : ℝ → ℝ := fun t => G (projIcc a b hab.le t)
  have hcE : Continuous E := (continuousOn_iff_continuous_domRestrict.mp hG).comp continuous_projIcc
  have heE (t : ℝ) (ht : t ∈ Icc a b) : E t=G t := by
    dsimp [E]
    rw [projIcc_of_mem hab.le ht]
  let H : ℝ → ℝ := fun t => ∫ s in a..t, E s
  have hdH (t : ℝ) : HasDerivAt H (E t) t :=
    intervalIntegral.integral_hasDerivAt_right (hcE.intervalIntegrable a t)
      hcE.aestronglyMeasurable.stronglyMeasurableAtFilter hcE.continuousAt
  have hcH : Continuous H := (fun t => (hdH t).continuousAt) |> continuous_iff_continuousAt.mpr
  have hbound (t : ℝ) (ht : t ∈ Icc a b) (ε : ℝ) (hε : 0 < ε) :
      |(F t-H t)-(F a-H a)| ≤ ε*(t-a) := by
    have hev := Metric.tendstoUniformlyOn_iff.mp hg ε hε
    have hbnd : ∀ᶠ n in atTop, |(f n t-H t)-(f n a-H a)| ≤ ε*(t-a) := by
      filter_upwards [hev] with n hn
      have hh := norm_image_sub_le_of_norm_deriv_right_le_segment
        ((hc n).sub hcH.continuousOn)
        (fun s hs => (hd n s hs).sub (hdH s).hasDerivWithinAt)
        (C:=ε) (fun s hs => ?_) t ht
      · simpa only [Real.norm_eq_abs,Pi.sub_apply] using hh
      · rw [Real.norm_eq_abs,heE s ⟨hs.1,hs.2.le⟩,abs_sub_comm]
        exact (hn s hs).le
    have hl := (((hv t ht).sub_const (H t)).sub
      ((hv a ⟨le_rfl,hab.le⟩).sub_const (H a))).abs
    exact le_of_tendsto hl hbnd
  have heq (t : ℝ) (ht : t ∈ Icc a b) : F t=F a-H a+H t := by
    have hlim : Tendsto (fun n : ℕ => (1/((n:ℝ)+1))*(t-a)) atTop (𝓝 (0*(t-a))) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (t-a)
    have hh : |(F t-H t)-(F a-H a)| ≤ 0 := by
      simpa using ge_of_tendsto' hlim (fun n => hbound t ht (1/((n:ℝ)+1)) (by positivity))
    have hz := abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
    linarith
  intro t ht
  have he : F =ᶠ[𝓝 t] (fun s => F a-H a+H s) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact heq s ⟨hs.1.le,hs.2.le⟩
  have hh := ((hdH t).const_add (F a-H a)).congr_of_eventuallyEq he
  rwa [heE t ⟨ht.1.le,ht.2.le⟩] at hh
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
lemma tendstoUniformlyOn_mul_bounded {α : Type*} {s : Set α}
    {f g : ℕ → α → ℝ} {F G : α → ℝ} {A B : ℝ}
    (hf : TendstoUniformlyOn f F atTop s) (hg : TendstoUniformlyOn g G atTop s)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfb : ∀ n x, x ∈ s → |f n x| ≤ A) (hGb : ∀ x ∈ s, |G x| ≤ B) :
    TendstoUniformlyOn (fun n x => f n x*g n x) (fun x => F x*G x) atTop s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ := ε/(A+B+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have heq : δ*(A+B+1)=ε := div_mul_cancel₀ ε (by positivity)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hf δ hδ,
    Metric.tendstoUniformlyOn_iff.mp hg δ hδ] with n hn hm x hx
  rw [Real.dist_eq]
  have hfδ : |F x-f n x| < δ := by simpa only [Real.dist_eq] using hn x hx
  have hgδ : |G x-g n x| < δ := by simpa only [Real.dist_eq] using hm x hx
  calc
    |F x*G x-f n x*g n x| = |(F x-f n x)*G x+f n x*(G x-g n x)| := by ring_nf
    _ ≤ |F x-f n x| *|G x|+|f n x| *|G x-g n x| := by simpa only [abs_mul] using abs_add_le ((F x-f n x)*G x) (f n x*(G x-g n x))
    _ ≤ δ*B+A*δ := add_le_add
      (mul_le_mul hfδ.le (hGb x hx) (abs_nonneg _) hδ.le)
      (mul_le_mul (hfb n x hx) hgδ.le (abs_nonneg _) hA)
    _ < ε := by nlinarith
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
lemma CylinderConvergence.time_slice {f : ℕ → ℝ → ℝ → ℝ} {F : ℝ → ℝ → ℝ} {S : Set ℝ}
    (hf : CylinderConvergence f F S) (x : ℝ) :
    TendstoUniformlyOn (fun n t => f n t x) (fun t => F t x) atTop S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hf (|x|+1) (by positivity)) ε hε] with n hn t ht
  exact hn (t,x) ⟨ht,by linarith [neg_abs_le x],by linarith [le_abs_self x]⟩

lemma gaussian_c2_limit_time {u m : ℝ → ℝ} {A B C κ Q : ℝ}
    (hQ : 0 < Q) (hu : RowAnalyticTerminal u A B C κ Q)
    {rs : ℕ → List (ℝ × ℝ)}
    (hrs : ∀ n, ∀ r ∈ rs n, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (hT : ∀ n, gaussianStepTime (rs n)=Q)
    (hm : ContinuousOn m (Icc 0 Q))
    (hmn : TendstoUniformlyOn (fun n => gaussianStepCoefficient (rs n)) m atTop (Icc 0 Q))
    {F : ℝ → ℝ → ℝ}
    (hc1 : ContinuousOn (fun p : ℝ × ℝ => deriv (F p.1) p.2) (Icc 0 Q ×ˢ univ))
    (hc2 : ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (F p.1)) p.2) (Icc 0 Q ×ˢ univ))
    (hv : CylinderConvergence (fun n => gaussianStepPath (rs n) u) F (Icc 0 Q))
    (hd1 : CylinderConvergence (fun n t => deriv (gaussianStepPath (rs n) u t)) (fun t => deriv (F t)) (Icc 0 Q))
    (hd2 : CylinderConvergence (fun n t => deriv (deriv (gaussianStepPath (rs n) u t)))
      (fun t => deriv (deriv (F t))) (Icc 0 Q)) :
    ∀ t ∈ Ioo 0 Q, ∀ x, HasDerivAt (fun r => F r x)
      (-(1/2:ℝ)*(deriv (deriv (F t)) x+m t*(deriv (F t) x)^2)) t := by
  obtain ⟨D,L,hD,hL,hpath⟩ := gaussian_step_path A B C κ Q hQ hu.2.1 hu.2.2.1 hu.2.2.2.1 hu.2.2.2.2.1
  have hp (n : ℕ) := hpath u hu (rs n) (hrs n) (hT n).le
  have hspace (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 Q) :=
    (hp n).2.2.2 t ht.1 (by rw [hT]; exact ht.2)
  have hslope (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 Q) (x : ℝ) := ((hspace n t ht).2.2 x).1
  have hFslope (t : ℝ) (ht : t ∈ Icc 0 Q) (x : ℝ) : |deriv (F t) x| ≤ L*(1+|x|) :=
    le_of_tendsto (hd1.tendsto_at ht x).abs (Eventually.of_forall (fun n => hslope n t ht x))
  intro t ht x
  let g : ℕ → ℝ → ℝ := fun n t => -(1/2:ℝ)*(deriv (deriv (gaussianStepPath (rs n) u t)) x+
    gaussianStepRightCoefficient (rs n) t*(deriv (gaussianStepPath (rs n) u t) x)^2)
  let G : ℝ → ℝ := fun t => -(1/2:ℝ)*(deriv (deriv (F t)) x+m t*(deriv (F t) x)^2)
  have hc (n : ℕ) : ContinuousOn (fun t => gaussianStepPath (rs n) u t x) (Icc 0 Q) :=
    (gaussianStepPath_jointly_continuous hD hL (hT n) (hp n).2.2.1
      (fun s hs hsT => ⟨(hspace n s ⟨hs,by rwa [hT] at hsT⟩).1,
        fun y => hslope n s ⟨hs,by rwa [hT] at hsT⟩ y⟩)).comp
      (continuous_id.prodMk continuous_const).continuousOn (fun s hs => ⟨hs,mem_univ x⟩)
  have hjet1 := (hd1.time_slice x).mono Ico_subset_Icc_self
  have hjet2 := (hd2.time_slice x).mono Ico_subset_Icc_self
  have hsq : TendstoUniformlyOn (fun n s => (deriv (gaussianStepPath (rs n) u s) x)^2)
      (fun s => (deriv (F s) x)^2) atTop (Ico 0 Q) := by
    simpa only [pow_two] using tendstoUniformlyOn_mul_bounded hjet1 hjet1
      (by positivity : 0 ≤ L*(1+|x|)) (by positivity : 0 ≤ L*(1+|x|))
      (fun n s hs => hslope n s ⟨hs.1,hs.2.le⟩ x)
      (fun s hs => hFslope s ⟨hs.1,hs.2.le⟩ x)
  have hprod := tendstoUniformlyOn_mul_bounded (gaussianStepRightCoefficient_tendsto hm hmn) hsq
    (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 ≤ (L*(1+|x|))^2)
    (fun n s _ => by rw [abs_of_nonneg (gaussianStepRightCoefficient_bounds (hrs n) s).1]; exact (gaussianStepRightCoefficient_bounds (hrs n) s).2)
    (fun s hs => by
      rw [abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ L*(1+|x|))).mpr (hFslope s ⟨hs.1,hs.2.le⟩ x))
  have hg : TendstoUniformlyOn g G atTop (Ico 0 Q) := by
    exact (Real.uniformContinuous_const_mul (x := -(1/2:ℝ))).comp_tendstoUniformlyOn (hjet2.add hprod)
  have hG : ContinuousOn G (Icc 0 Q) := by
    have h1 := hc1.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => (show (s,x) ∈ Icc 0 Q ×ˢ univ from ⟨hs,mem_univ x⟩))
    have h2 := hc2.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => (show (s,x) ∈ Icc 0 Q ×ˢ univ from ⟨hs,mem_univ x⟩))
    exact (h2.add (hm.mul (h1.pow 2))).const_mul _
  exact hasDerivAt_of_uniform_right_derivatives hQ hc
    (fun n s hs => gaussianStepPath_right_pde hQ hu (hrs n) (hT n).le (by rwa [hT]) x)
    (fun s hs => hv.tendsto_at hs x) hg hG t ht
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
lemma gaussianStepPath_value_bounds {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hQ : 0 < Q) (hu : RowAnalyticTerminal u A B C κ Q)
    {rs : List (ℝ × ℝ)} (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (hT : gaussianStepTime rs=Q) {t : ℝ} (ht : t ∈ Icc 0 Q) (x : ℝ) :
    -A*(1+x^2+Q-t) ≤ gaussianStepPath rs u t x ∧ gaussianStepPath rs u t x ≤ B := by
  obtain ⟨hv,hvT⟩ := gaussianStepRemainder_valid hrs ht.1
  rw [hT,max_eq_left (sub_nonneg.mpr ht.2)] at hvT
  have hvQ : gaussianStepTime (gaussianStepRemainder rs t) ≤ Q := by rw [hvT]; linarith [ht.1]
  have hb := ((gaussian_step_bounds u A B C κ Q hQ hu _ hv hvQ).2.2 x).1
  change -A*(1+x^2+gaussianStepTime (gaussianStepRemainder rs t)) ≤ gaussianStepPath rs u t x ∧ gaussianStepPath rs u t x ≤ B at hb
  simpa only [hvT,add_sub_assoc] using hb

lemma gaussian_classical_limit {u m : ℝ → ℝ} {A B C κ Q L : ℝ}
    (hQ : 0 < Q) (hu : RowAnalyticTerminal u A B C κ Q) (hL : 0 ≤ L)
    {rs : ℕ → List (ℝ × ℝ)}
    (hrs : ∀ n, ∀ r ∈ rs n, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (hT : ∀ n, gaussianStepTime (rs n)=Q)
    (hm : ContinuousOn m (Icc 0 Q))
    (hmn : TendstoUniformlyOn (fun n => gaussianStepCoefficient (rs n)) m atTop (Icc 0 Q))
    (hLn : ∀ n t, t ∈ Icc 0 Q → ∀ x, |deriv (gaussianStepPath (rs n) u t) x| ≤ L*(1+|x|)) :
    ∃ F : ℝ → ℝ → ℝ, RowClassicalVarianceSolution Q u m F ∧
      (∀ t ∈ Icc 0 Q, ∀ x, -A*(1+x^2+Q-t) ≤ F t x ∧ F t x ≤ B ∧
        |deriv (F t) x| ≤ L*(1+|x|) ∧
        -C ≤ deriv (deriv (F t)) x ∧ deriv (deriv (F t)) x ≤ κ/(1-κ*(Q-t))) ∧
      CylinderConvergence (fun n => gaussianStepPath (rs n) u) F (Icc 0 Q) := by
  obtain ⟨F,hc,hc1,hc2,hd,hv,h1,h2⟩ := gaussian_step_c2_limit hQ hu hrs hT hmn
  have ht := gaussian_c2_limit_time hQ hu hrs hT hm hmn hc1 hc2 hv h1 h2
  have hb (t : ℝ) (ht : t ∈ Icc 0 Q) (x : ℝ) :
      -A*(1+x^2+Q-t) ≤ F t x ∧ F t x ≤ B ∧ |deriv (F t) x| ≤ L*(1+|x|) ∧
      -C ≤ deriv (deriv (F t)) x ∧ deriv (deriv (F t)) x ≤ κ/(1-κ*(Q-t)) := by
    have hb0 (n : ℕ) := gaussianStepPath_value_bounds hQ hu (hrs n) (hT n) ht x
    have hb2 (n : ℕ) : -C ≤ deriv (deriv (gaussianStepPath (rs n) u t)) x ∧
        deriv (deriv (gaussianStepPath (rs n) u t)) x ≤ κ/(1-κ*(Q-t)) := by
      obtain ⟨hv',hvT⟩ := gaussianStepRemainder_valid (hrs n) ht.1
      rw [hT,max_eq_left (sub_nonneg.mpr ht.2)] at hvT
      have hvQ : gaussianStepTime (gaussianStepRemainder (rs n) t) ≤ Q := by rw [hvT]; linarith [ht.1]
      change -C ≤ deriv (deriv (gaussianRowComposition (gaussianStepRemainder (rs n) t) u)) x ∧
        deriv (deriv (gaussianRowComposition (gaussianStepRemainder (rs n) t) u)) x ≤ κ/(1-κ*(Q-t))
      have hh := ((gaussian_step_bounds u A B C κ Q hQ hu _ hv' hvQ).2.2 x).2
      simpa only [hvT] using hh
    exact ⟨ge_of_tendsto' (hv.tendsto_at ht x) (fun n => (hb0 n).1),
      le_of_tendsto' (hv.tendsto_at ht x) (fun n => (hb0 n).2),
      le_of_tendsto' (h1.tendsto_at ht x).abs (fun n => hLn n t ht x),
      ge_of_tendsto' (h2.tendsto_at ht x) (fun n => (hb2 n).1),
      le_of_tendsto' (h2.tendsto_at ht x) (fun n => (hb2 n).2)⟩
  have hterm (x : ℝ) : F Q x=u x := by
    obtain ⟨D,L',hD,hL',hpath⟩ := gaussian_step_path A B C κ Q hQ hu.2.1 hu.2.2.1 hu.2.2.2.1 hu.2.2.2.2.1
    have he (n : ℕ) : gaussianStepPath (rs n) u Q x=u x := by
      simpa only [hT n] using (hpath u hu (rs n) (hrs n) (hT n).le).2.1 x
    exact tendsto_nhds_unique (hv.tendsto_at ⟨hQ.le,le_rfl⟩ x)
      (by simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => u x) atTop (𝓝 (u x))))
  have hA : 0 ≤ A := hu.2.1
  have hvalueK : 0 ≤ |B|+A*(1+Q) := by positivity
  have hK : 0 ≤ |B|+A*(1+Q)+L := by positivity
  have hg (t : ℝ) (ht : t ∈ Icc 0 Q) (x : ℝ) :
      |F t x| ≤ (|B|+A*(1+Q)+L)*(1+x^2) ∧ |deriv (F t) x| ≤ (|B|+A*(1+Q)+L)*(1+|x|) := by
    have hval := le_of_tendsto' (hv.tendsto_at ht x).abs
      (fun n => gaussianStepPath_global_value_bound hQ hu (hrs n) (hT n) ht x)
    constructor
    · exact hval.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    · exact (hb t ht x).2.2.1.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  exact ⟨F,⟨hc,hc1,hc2,hd,ht,hterm,_,hK,hg⟩,hb,hv⟩
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming

 
def gaussianGrid (m : ℝ → ℝ) (a h : ℝ) : ℕ → List (ℝ × ℝ)
  | 0 => []
  | n+1 => (m a,h)::gaussianGrid m (a+h) h n

lemma gaussianGrid_time (m : ℝ → ℝ) (a h : ℝ) (n : ℕ) :
    gaussianStepTime (gaussianGrid m a h n)=(n:ℝ)*h := by
  induction n generalizing a with
  | zero => simp [gaussianGrid,gaussianStepTime]
  | succ n ih =>
    change h+gaussianStepTime (gaussianGrid m (a+h) h n)=_
    rw [ih,Nat.cast_add,Nat.cast_one]
    ring

lemma gaussianGrid_valid {m : ℝ → ℝ} {a h : ℝ} (n : ℕ) (hh : 0 ≤ h)
    (hm : ∀ s ∈ Icc a (a+(n:ℝ)*h), 0 ≤ m s ∧ m s ≤ 1) :
    ∀ r ∈ gaussianGrid m a h n, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2 := by
  induction n generalizing a with
  | zero => simp [gaussianGrid]
  | succ n ih =>
    intro r hr
    rcases List.mem_cons.mp hr with he | he
    · subst r
      exact ⟨(hm a ⟨le_rfl,le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hh)⟩).1,(hm a ⟨le_rfl,le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hh)⟩).2,hh⟩
    · apply ih (a:=a+h) _ r he
      intro s hs
      apply hm s
      constructor
      · linarith [hs.1]
      · rw [Nat.cast_add,Nat.cast_one]
        linarith [hs.2]

lemma gaussianGrid_coefficient_sample {m : ℝ → ℝ} {a h t : ℝ} (n : ℕ)
    (hn : 0 < n) (hh : 0 ≤ h) (ht : t ∈ Icc 0 ((n:ℝ)*h)) :
    ∃ s ∈ Icc a (a+(n:ℝ)*h), |s-(a+t)| ≤ h ∧
      gaussianStepCoefficient (gaussianGrid m a h n) t=m s := by
  induction n generalizing a t with
  | zero => omega
  | succ n ih =>
    by_cases hth : t ≤ h
    · refine ⟨a,⟨le_rfl,le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hh)⟩,?_,?_⟩
      · rw [show a-(a+t) = -t by ring,abs_neg,abs_of_nonneg ht.1]
        exact hth
      · simp only [gaussianGrid,gaussianStepCoefficient,ite_eq_left hth]
    · have hlt : h < t := lt_of_not_ge hth
      have hn' : 0 < n := by
        by_contra hc
        have hz : n=0 := by omega
        simp only [hz,Nat.zero_add,Nat.cast_one,one_mul] at ht
        exact not_lt_of_ge ht.2 hlt
      have ht' : t-h ∈ Icc 0 ((n:ℝ)*h) := by
        rw [Nat.cast_add,Nat.cast_one] at ht
        constructor <;> nlinarith [ht.2]
      obtain ⟨s,hs,hd,he⟩ := ih (a:=a+h) hn' ht'
      refine ⟨s,⟨by linarith [hs.1],?_⟩,?_,?_⟩
      · rw [Nat.cast_add,Nat.cast_one]
        linarith [hs.2]
      · simpa only [show (a+h)+(t-h)=a+t by ring] using hd
      · simpa only [gaussianGrid,gaussianStepCoefficient,ite_eq_right hth] using he

lemma exists_gaussian_grid_approximation {Q : ℝ} (hQ : 0 < Q) {m : ℝ → ℝ}
    (hm : ContinuousOn m (Icc 0 Q)) (hb : ∀ t ∈ Icc 0 Q, 0 ≤ m t ∧ m t ≤ 1) :
    ∃ rs : ℕ → List (ℝ × ℝ),
      (∀ n, ∀ r ∈ rs n, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) ∧
      (∀ n, gaussianStepTime (rs n)=Q) ∧
      TendstoUniformlyOn (fun n => gaussianStepCoefficient (rs n)) m atTop (Icc 0 Q) := by
  let h : ℕ → ℝ := fun n => Q/((n:ℝ)+1)
  have hh (n : ℕ) : 0 ≤ h n := by dsimp [h]; positivity
  have hlen (n : ℕ) : ((n+1:ℕ):ℝ)*h n=Q := by
    dsimp [h]
    rw [Nat.cast_add,Nat.cast_one]
    exact mul_div_cancel₀ Q (by positivity)
  let rs : ℕ → List (ℝ × ℝ) := fun n => gaussianGrid m 0 (h n) (n+1)
  refine ⟨rs,?_,?_,?_⟩
  · intro n
    apply gaussianGrid_valid (n+1) (hh n)
    simpa only [hlen,zero_add] using hb
  · intro n
    exact (gaussianGrid_time m 0 (h n) (n+1)).trans (hlen n)
  · have hlim : Tendsto h atTop (𝓝 0) := by
      have hhlim := (tendsto_const_nhds (x:=Q)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
      simpa only [mul_one_div,mul_zero] using hhlim
    have huc := Metric.uniformContinuousOn_iff.mp (isCompact_Icc.uniformContinuousOn_of_continuous hm)
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨δ,hδ,hnear⟩ := huc ε hε
    filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with n hn t ht
    have ht' : t ∈ Icc 0 (((n+1:ℕ):ℝ)*h n) := by simpa only [hlen] using ht
    obtain ⟨s,hs,hd,he⟩ := gaussianGrid_coefficient_sample (m:=m) (a:=0) (n+1) (by omega) (hh n) ht'
    have hs' : s ∈ Icc 0 Q := by simpa only [hlen,zero_add] using hs
    
    rw [he]
    apply hnear t ht s hs'
    rw [Real.dist_eq,abs_sub_comm]
    exact (by simpa only [zero_add] using hd : |s-t| ≤ h n).trans_lt hn
end MicroscopicJamming

end

end OAI
