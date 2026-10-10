import Mathlib
import OAI.Analysis.PathSelection.ContourPreparation

namespace OAI

/-! Convergence of contour sums, preparation coefficients and division remainders. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

namespace PathSelection.PreparationLimit

open Complex PathSelection.Preparation
open scoped Real


lemma tendstoUniformlyOn_circleIntegral {ι A : Type*} {l : Filter ι}
    {S : Set A} {F : ι → A → ℂ → ℂ} {f : A → ℂ → ℂ} {r : ℝ}
    (hr : 0<r)
    (hF : ∀ᶠ i in l, ∀ a∈S, ContinuousOn (F i a) (sphere 0 r))
    (hf : ∀ a∈S, ContinuousOn (f a) (sphere 0 r))
    (h : TendstoUniformlyOn (fun i (p : A × ℂ) => F i p.1 p.2)
      (fun p => f p.1 p.2) l (S ×ˢ sphere 0 r)) :
    TendstoUniformlyOn (fun i a => ∮ z in C(0,r), F i a z)
      (fun a => ∮ z in C(0,r), f a z) l S := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  have hC : 0<2*π*r := by positivity
  let δ := ε/(2*(2*π*r))
  have hδ : 0<δ := div_pos hε (mul_pos (by norm_num) hC)
  filter_upwards [h δ hδ,hF] with i hi hiF
  intro a ha
  rw [dist_eq_norm,← circleIntegral.integral_sub ((hf a ha).circleIntegrable hr.le)
    ((hiF a ha).circleIntegrable hr.le)]
  have hb := circleIntegral.norm_integral_le_of_norm_le_const hr.le
    (f := fun z => f a z-F i a z) (C := δ)
    (fun z hz => (show ‖f a z-F i a z‖<δ from by
      simpa only [dist_eq_norm] using hi (a,z) ⟨ha,hz⟩).le)
  have he : (2*π*r)*δ=ε/2 := by dsimp [δ]; field_simp
  exact hb.trans_lt (he ▸ by linarith)

lemma circleIntegral_tendsto {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {r : ℝ} (hr : 0<r)
    (hF : ∀ᶠ i in l, ContinuousOn (F i) (sphere 0 r))
    (hf : ContinuousOn f (sphere 0 r))
    (h : TendstoUniformlyOn F f l (sphere 0 r)) :
    Tendsto (fun i => ∮ z in C(0,r), F i z) l (𝓝 (∮ z in C(0,r), f z)) := by
  have hh := tendstoUniformlyOn_circleIntegral (A := Unit) (S := univ)
    (F := fun i _ z => F i z) (f := fun _ z => f z) hr
    (hF.mono (fun i hi _ _ => hi)) (fun _ _ => hf) (by
      rw [Metric.tendstoUniformlyOn_iff] at h ⊢
      intro ε hε
      filter_upwards [h ε hε] with i hi p hp
      exact hi p.2 hp.2)
  exact hh.tendsto_at (mem_univ ())

lemma eventual_uniform_nonzero {ι X : Type*} [TopologicalSpace X]
    {l : Filter ι} {F : ι → X → ℂ} {f : X → ℂ} {K : Set X}
    (hK : IsCompact K) (hf : ContinuousOn f K) (hnz : ∀ x∈K, f x≠0)
    (h : TendstoUniformlyOn F f l K) :
    ∀ᶠ i in l, ∀ x∈K, F i x≠0 := by
  by_cases hne : K.Nonempty
  · obtain ⟨x,hx,hm⟩ := hK.exists_isMinOn hne hf.norm
    have hxpos : 0<‖f x‖ := norm_pos_iff.mpr (hnz x hx)
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp h) ‖f x‖ hxpos] with i hi
    intro y hy he
    have hh := hi y hy
    rw [he,dist_zero_right] at hh
    exact (not_lt_of_ge (hm hy)) hh
  · filter_upwards with i x hx
    exact (hne ⟨x,hx⟩).elim

lemma tendstoPowerSum {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ} {r : ℝ}
    (hU : IsOpen U) (hr : 0<r) (hKU : sphere (0:ℂ) r⊆U)
    (hF : ∀ᶠ i in l, AnalyticOnNhd ℂ (F i) U)
    (hf : AnalyticOnNhd ℂ f U)
    (hnz : ∀ z∈sphere (0:ℂ) r, f z≠0)
    (h : TendstoLocallyUniformlyOn F f l U) (n : ℕ) :
    Tendsto (fun i => contourPowerSum (F i) r n) l (𝓝 (contourPowerSum f r n)) := by
  have hK := isCompact_sphere (0:ℂ) r
  have hc {G : ι → ℂ → ℂ} {g : ℂ → ℂ} :
      TendstoLocallyUniformlyOn G g l (sphere 0 r) ↔
      TendstoUniformlyOn G g l (sphere 0 r) :=
    tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK
  have hd := h.deriv (hF.mono (fun i hi => hi.differentiableOn)) hU
  have hf' := hf.mono hKU
  have hd' := hf.deriv.continuousOn.mono hKU
  have hdiv := (hd.mono hKU).div₀ (h.mono hKU) hd' hf'.continuousOn hnz
  have hpow : TendstoLocallyUniformlyOn (fun _ : ι => fun z : ℂ => z^n)
      (fun z => z^n) l (sphere 0 r) := by
    apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards with i z hz
    simpa using hε
  have hint := hpow.mul₀ hdiv (continuousOn_id.pow _)
    (hd'.div hf'.continuousOn hnz)
  have hev := eventual_uniform_nonzero hK hf'.continuousOn hnz (hc.mp (h.mono hKU))
  have hcF : ∀ᶠ i in l, ContinuousOn (fun z => z^n * (deriv (F i) z/F i z)) (sphere 0 r) := by
    filter_upwards [hF,hev] with i hi hn
    exact (continuousOn_id.pow _).mul
      ((hi.deriv.continuousOn.mono hKU).div (hi.continuousOn.mono hKU) hn)
  have hcf : ContinuousOn (fun z => z^n * (deriv f z/f z)) (sphere 0 r) :=
    (continuousOn_id.pow _).mul (hd'.div hf'.continuousOn hnz)
  have ht := circleIntegral_tendsto hr hcF hcf (hc.mp hint)
  simpa only [contourPowerSum,mul_div_assoc] using ht.const_mul ((2*π*I)⁻¹)

lemma tendsto_newtonEsymm {ι : Type*} {l : Filter ι} {s : ι → ℕ → ℂ} {t : ℕ → ℂ}
    (h : ∀ k, Tendsto (fun i => s i k) l (𝓝 (t k))) (n : ℕ) :
    Tendsto (fun i => newtonEsymm (s i) n) l (𝓝 (newtonEsymm t n)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [show (fun i => newtonEsymm (s i) n) =
      (fun i => if n=0 then 1 else (n:ℂ)⁻¹ * (-1)^(n+1) *
        ∑ a ∈ (Finset.HasAntidiagonal.antidiagonal n).filter (fun a => a.1<n),
          if h : a.1<n then (-1)^a.1 * newtonEsymm (s i) a.1 * s i a.2 else 0) by
      funext i; rw [newtonEsymm],newtonEsymm]
    split_ifs with hn
    · exact tendsto_const_nhds
    · apply Filter.Tendsto.const_mul
      apply tendsto_finsetSum
      intro a ha
      split_ifs with ha'
      · exact ((ih a.1 ha').const_mul _).mul (h a.2)
      · exact tendsto_const_nhds

lemma eventually_count_eq {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {r : ℝ} (hr : 0<r)
    (hF : ∀ᶠ i in l, AnalyticOnNhd ℂ (F i) (closedBall 0 r))
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r))
    (hnz : ∀ z∈sphere (0:ℂ) r, f z≠0)
    (h : TendstoUniformlyOn F f l (sphere 0 r)) :
    ∀ᶠ i in l, contourPowerSum (F i) r 0 = contourPowerSum f r 0 := by
  have hne : (sphere (0:ℂ) r).Nonempty := ⟨(r:ℂ),by
    simp only [mem_sphere_zero_iff_norm,norm_real,Real.norm_eq_abs,abs_of_pos hr]⟩
  obtain ⟨z,hz,hm⟩ := (isCompact_sphere (0:ℂ) r).exists_isMinOn hne
    (hf.continuousOn.mono sphere_subset_closedBall).norm
  have hzpos : 0<‖f z‖ := norm_pos_iff.mpr (hnz z hz)
  filter_upwards [hF,(Metric.tendstoUniformlyOn_iff.mp h) ‖f z‖ hzpos] with i hi hi'
  apply (contour_zero_count_eq_of_norm_sub_lt hr hf hi ?_).symm
  intro w hw
  have hh := hi' w hw
  rw [dist_comm,dist_eq_norm] at hh
  exact hh.trans_le (hm hw)

lemma const_locallyUniform {ι X : Type*} [TopologicalSpace X] {l : Filter ι}
    (f : X → ℂ) (S : Set X) : TendstoLocallyUniformlyOn (fun _ : ι => f) f l S := by
  apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards with i x hx
  simpa using hε

lemma tendsto_preparation_coeff {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {r : ℝ}
    (h : ∀ n, Tendsto (fun i => contourPowerSum (F i) r n) l (𝓝 (contourPowerSum f r n)))
    (d k : ℕ) :
    Tendsto (fun i => (preparationPolynomial (F i) r d).coeff k) l
      (𝓝 ((preparationPolynomial f r d).coeff k)) := by
  classical
  simp only [preparationPolynomial,finsetSum_coeff,coeff_C_mul_X_pow]
  apply tendsto_finsetSum
  intro n hn
  split_ifs
  · exact (tendsto_newtonEsymm h (d-n)).const_mul _
  · exact tendsto_const_nhds

lemma locallyUniform_finset_sum {ι X B : Type*} [TopologicalSpace X]
    {l : Filter ι} {S : Set X} {F : B → ι → X → ℂ} {f : B → X → ℂ}
    (s : Finset B) (h : ∀ b∈s, TendstoLocallyUniformlyOn (F b) (f b) l S) :
    TendstoLocallyUniformlyOn (fun i x => ∑ b∈s, F b i x)
      (fun x => ∑ b∈s, f b x) l S := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const_locallyUniform (l := l) (fun _ : X => (0:ℂ)) S
  | @insert b s hb ih =>
    simp only [Finset.sum_insert hb]
    exact (h b (Finset.mem_insert_self _ _)).add
      (ih (fun c hc => h c (Finset.mem_insert_of_mem hc)))

lemma tendsto_preparation_eval {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {r : ℝ}
    (h : ∀ n, Tendsto (fun i => contourPowerSum (F i) r n) l (𝓝 (contourPowerSum f r n)))
    (d : ℕ) :
    TendstoLocallyUniformlyOn (fun i z => (preparationPolynomial (F i) r d).eval z)
      (fun z => (preparationPolynomial f r d).eval z) l univ := by
  classical
  simp only [preparationPolynomial,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X]
  apply locallyUniform_finset_sum
  intro k hk
  have hc := ((tendsto_newtonEsymm h (d-k)).const_mul ((-1:ℂ)^(d-k))).tendstoUniformlyOn_const
    (s := (univ : Set ℂ))
  exact hc.tendstoLocallyUniformlyOn.mul₀ (const_locallyUniform (fun z : ℂ => z^k) univ)
    continuousOn_const (continuousOn_id.pow _)

 

theorem tendsto_divisionQuotient {ι : Type*} {l : Filter ι}
    {G : ι → ℂ → ℂ} {g : ℂ → ℂ} {P : ι → ℂ[X]} {p : ℂ[X]} {r : ℝ}
    (hr : 0<r)
    (hG : ∀ᶠ i in l, ContinuousOn (G i) (sphere 0 r))
    (hg : ContinuousOn g (sphere 0 r))
    (hnz : ∀ w∈sphere (0:ℂ) r, p.eval w≠0)
    (hlimG : TendstoUniformlyOn G g l (sphere 0 r))
    (hlimP : TendstoUniformlyOn (fun i w => (P i).eval w) p.eval l (sphere 0 r)) :
    TendstoLocallyUniformlyOn (fun i y => divisionQuotient (G i) (P i) r y)
      (divisionQuotient g p r) l (ball 0 r) := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball]
  intro K hKb hK
  let S : Set (ℂ × ℂ) := K ×ˢ sphere 0 r
  have hS : IsCompact S := hK.prod (isCompact_sphere _ _)
  have hn (z : ℂ × ℂ) (hz : z∈S) : z.2-z.1≠0 := by
    apply sub_ne_zero.mpr
    intro he
    have hlt := mem_ball_zero_iff.mp (hKb hz.1)
    have heq := mem_sphere_zero_iff_norm.mp hz.2
    rw [he] at heq
    exact (ne_of_lt hlt) heq
  have cg : ContinuousOn (fun z : ℂ × ℂ => g z.2) S :=
    hg.comp continuousOn_snd (fun z hz => hz.2)
  have cp : ContinuousOn (fun z : ℂ × ℂ => p.eval z.2) S :=
    p.continuous.continuousOn.comp continuousOn_snd (fun _ _ => mem_univ _)
  have cn : ContinuousOn (fun z : ℂ × ℂ => z.2-z.1) S :=
    continuousOn_snd.sub continuousOn_fst
  have hg' := hlimG.tendstoLocallyUniformlyOn.comp Prod.snd
    (t := S) (fun z hz => hz.2) continuousOn_snd
  have hp' := hlimP.tendstoLocallyUniformlyOn.comp Prod.snd
    (t := S) (fun z hz => hz.2) continuousOn_snd
  have hden := hp'.mul₀ (const_locallyUniform (fun z : ℂ × ℂ => z.2-z.1) S) cp cn
  have hd := hg'.div₀ hden cg (cp.mul cn)
    (fun z hz => mul_ne_zero (hnz z.2 hz.2) (hn z hz))
  have hd' : TendstoUniformlyOn
      (fun i (z : ℂ × ℂ) => G i z.2 / ((P i).eval z.2 * (z.2-z.1)))
      (fun z : ℂ × ℂ => g z.2 / (p.eval z.2 * (z.2-z.1))) l S :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hS).mp hd
  have hev := eventual_uniform_nonzero (isCompact_sphere (0:ℂ) r)
    p.continuous.continuousOn hnz hlimP
  have hci : ∀ᶠ i in l, ∀ y∈K,
      ContinuousOn (fun w => G i w / ((P i).eval w*(w-y))) (sphere 0 r) := by
    filter_upwards [hG,hev] with i hi hiP
    intro y hy
    exact hi.div ((P i).continuous.continuousOn.mul
      (continuousOn_id.sub continuousOn_const))
      (fun w hw => mul_ne_zero (hiP w hw) (hn (y,w) ⟨hy,hw⟩))
  have hcg : ∀ y∈K,
      ContinuousOn (fun w => g w / (p.eval w*(w-y))) (sphere 0 r) := by
    intro y hy
    exact hg.div (p.continuous.continuousOn.mul
      (continuousOn_id.sub continuousOn_const))
      (fun w hw => mul_ne_zero (hnz w hw) (hn (y,w) ⟨hy,hw⟩))
  have ht := tendstoUniformlyOn_circleIntegral hr hci hcg hd'
  have hqcont := (divisionQuotient_analyticOnNhd hr hg hnz).continuousOn.mono hKb
  have hcint : ContinuousOn (fun y => ∮ w in C(0,r), g w / (p.eval w*(w-y))) K := by
    have hc := hqcont.const_mul (2*π*I)
    convert hc using 1
    funext y
    simp only [divisionQuotient,← mul_assoc,mul_inv_cancel₀ (show (2*π*I:ℂ)≠0 by
      simp [Real.pi_ne_zero,I_ne_zero]),one_mul]
  have hscaled := (const_locallyUniform (l := l) (fun _ : ℂ => (2*π*I:ℂ)⁻¹) K).mul₀
    ht.tendstoLocallyUniformlyOn continuousOn_const hcint
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp hscaled

lemma tendsto_weighted_ratio_integral {ι : Type*} {l : Filter ι}
    {G : ι → ℂ → ℂ} {g : ℂ → ℂ} {P : ι → ℂ[X]} {p : ℂ[X]} {r : ℝ}
    (hr : 0<r) (hG : ∀ᶠ i in l, ContinuousOn (G i) (sphere 0 r))
    (hg : ContinuousOn g (sphere 0 r))
    (hnz : ∀ w∈sphere (0:ℂ) r, p.eval w≠0)
    (hlimG : TendstoUniformlyOn G g l (sphere 0 r))
    (hlimP : TendstoUniformlyOn (fun i w => (P i).eval w) p.eval l (sphere 0 r))
    {c : ι → ℂ} {c₀ : ℂ} (hc : Tendsto c l (𝓝 c₀)) (m : ℕ) :
    Tendsto (fun i => (2*π*I)⁻¹ * ∮ w in C(0,r),
      G i w / (P i).eval w * (c i * w^m)) l
      (𝓝 ((2*π*I)⁻¹ * ∮ w in C(0,r), g w / p.eval w * (c₀*w^m))) := by
  have hdiv := hlimG.tendstoLocallyUniformlyOn.div₀ hlimP.tendstoLocallyUniformlyOn
    hg p.continuous.continuousOn hnz
  have hcw := (hc.tendstoUniformlyOn_const (s := sphere (0:ℂ) r)).tendstoLocallyUniformlyOn.mul₀
    (const_locallyUniform (fun w : ℂ => w^m) (sphere 0 r))
    continuousOn_const (continuousOn_id.pow _)
  have hf := hdiv.mul₀ hcw (hg.div p.continuous.continuousOn hnz)
    (continuousOn_const.mul (continuousOn_id.pow _))
  have hev := eventual_uniform_nonzero (isCompact_sphere (0:ℂ) r)
    p.continuous.continuousOn hnz hlimP
  have hFi : ∀ᶠ i in l, ContinuousOn (fun w => G i w/(P i).eval w*(c i*w^m)) (sphere 0 r) := by
    filter_upwards [hG,hev] with i hi hiP
    exact (hi.div (P i).continuous.continuousOn hiP).mul
      (continuousOn_const.mul (continuousOn_id.pow _))
  exact (circleIntegral_tendsto hr hFi
    ((hg.div p.continuous.continuousOn hnz).mul
      (continuousOn_const.mul (continuousOn_id.pow _)))
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_sphere (0:ℂ) r)).mp hf)).const_mul _

 

theorem tendsto_divisionRemainder_coeff {ι : Type*} {l : Filter ι}
    {G : ι → ℂ → ℂ} {g : ℂ → ℂ} {P : ι → ℂ[X]} {p : ℂ[X]} {r : ℝ}
    (hr : 0<r) (hG : ∀ᶠ i in l, ContinuousOn (G i) (sphere 0 r))
    (hg : ContinuousOn g (sphere 0 r))
    (hnz : ∀ w∈sphere (0:ℂ) r, p.eval w≠0)
    (hlimG : TendstoUniformlyOn G g l (sphere 0 r))
    (hlimP : TendstoUniformlyOn (fun i w => (P i).eval w) p.eval l (sphere 0 r))
    (hcoeff : ∀ n, Tendsto (fun i => (P i).coeff n) l (𝓝 (p.coeff n)))
    (hdeg : ∀ᶠ i in l, (P i).natDegree=p.natDegree) (k : ℕ) :
    Tendsto (fun i => (divisionRemainder (G i) (P i) r).coeff k) l
      (𝓝 ((divisionRemainder g p r).coeff k)) := by
  classical
  have ht : Tendsto (fun i => ∑ n∈Finset.range (p.natDegree+1),
      ∑ j∈Finset.range n, if k=j then (2*π*I)⁻¹ * ∮ w in C(0,r),
        G i w / (P i).eval w * ((P i).coeff n * w^(n-1-j)) else 0) l
      (𝓝 (∑ n∈Finset.range (p.natDegree+1), ∑ j∈Finset.range n,
        if k=j then (2*π*I)⁻¹ * ∮ w in C(0,r),
          g w / p.eval w * (p.coeff n * w^(n-1-j)) else 0)) := by
    apply tendsto_finsetSum
    intro n hn
    apply tendsto_finsetSum
    intro j hj
    split_ifs
    · exact tendsto_weighted_ratio_integral hr hG hg hnz hlimG hlimP (hcoeff n) _
    · exact tendsto_const_nhds
  simp only [divisionRemainder,finsetSum_coeff,coeff_C_mul_X_pow]
  apply ht.congr'
  filter_upwards [hdeg] with i hi
  rw [hi]

 

theorem exists_preparation_circle {f : ℂ → ℂ} {U : Set ℂ} {d : ℕ}
    (hU : U∈𝓝 (0:ℂ)) (hf : AnalyticAt ℂ f 0)
    (hd : analyticOrderAt f 0=(d:ℕ∞)) :
    ∃ r : ℝ, 0<r ∧ closedBall (0:ℂ) r⊆U ∧
      AnalyticOnNhd ℂ f (closedBall 0 r) ∧
      (∀ z∈sphere (0:ℂ) r, f z≠0) ∧ contourPowerSum f r 0=(d:ℂ) := by
  obtain ⟨g,hg,hg0,heq⟩ := hf.analyticOrderAt_eq_natCast.mp hd
  have hn : ∀ᶠ z in 𝓝 (0:ℂ), g z≠0 := by
    exact hg.continuousAt.eventually_ne hg0
  have hev : ∀ᶠ z in 𝓝 (0:ℂ), z∈U ∧ AnalyticAt ℂ f z ∧ AnalyticAt ℂ g z ∧
      g z≠0 ∧ f z=z^d*g z := by
    filter_upwards [hU,hf.eventually_analyticAt,hg.eventually_analyticAt,hn,heq]
      with z hz hzf hzg hzn hze
    exact ⟨hz,hzf,hzg,hzn,by simpa only [sub_zero,smul_eq_mul] using hze⟩
  obtain ⟨ε,hε,hεs⟩ := Metric.mem_nhds_iff.mp hev
  let r := ε/2
  have hr : 0<r := half_pos hε
  have hh (z : ℂ) (hz : z∈closedBall (0:ℂ) r) :
      z∈U ∧ AnalyticAt ℂ f z ∧ AnalyticAt ℂ g z ∧ g z≠0 ∧ f z=z^d*g z := by
    apply hεs
    exact mem_ball.mpr ((mem_closedBall.mp hz).trans_lt (by dsimp [r]; linarith))
  have hfa : AnalyticOnNhd ℂ f (closedBall 0 r) := fun z hz => (hh z hz).2.1
  have hga : AnalyticOnNhd ℂ g (closedBall 0 r) := fun z hz => (hh z hz).2.2.1
  have hgn : ∀ z∈closedBall (0:ℂ) r, g z≠0 := fun z hz => (hh z hz).2.2.2.1
  have hfe : EqOn f (fun z => (X^d : ℂ[X]).eval z*g z) (closedBall 0 r) := by
    intro z hz
    simpa only [eval_pow,eval_X] using (hh z hz).2.2.2.2
  have hroot : ∀ z : ℂ, (X^d : ℂ[X]).eval z=0 → z∈ball 0 r := by
    intro z hz
    simp only [eval_pow,eval_X] at hz
    by_cases he : z=0
    · subst z
      exact mem_ball_self hr
    · exact (pow_ne_zero d he hz).elim
  refine ⟨r,hr,(fun z hz => (hh z hz).1),hfa,?_,?_⟩
  · intro z hz
    rw [(hh z (sphere_subset_closedBall hz)).2.2.2.2]
    apply mul_ne_zero (pow_ne_zero _ ?_) (hgn z (sphere_subset_closedBall hz))
    intro he
    have heq' := mem_sphere_zero_iff_norm.mp hz
    simp only [he,norm_zero] at heq'
    linarith
  · simpa only [natDegree_X_pow] using preparation_zero_count
      hr hfa (monic_X.pow d) hroot hga hgn hfe

lemma analyticOnNhd_iteratedDeriv {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (n : ℕ) : AnalyticOnNhd ℂ (iteratedDeriv n f) U := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

 

lemma tendstoLocallyUniformlyOn_iteratedDeriv {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : ∀ᶠ i in l, AnalyticOnNhd ℂ (F i) U)
    (h : TendstoLocallyUniformlyOn F f l U) (n : ℕ) :
    TendstoLocallyUniformlyOn (fun i => iteratedDeriv n (F i)) (iteratedDeriv n f) l U := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using h
  | succ n ih =>
    simpa only [iteratedDeriv_succ,Function.comp_def] using ih.deriv
      (hF.mono (fun i hi => (analyticOnNhd_iteratedDeriv hi n).differentiableOn)) hU
end PathSelection.PreparationLimit
end

end OAI
