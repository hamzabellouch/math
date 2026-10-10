import OAI.Analysis.AllenCahn.DefectLimits
import OAI.Analysis.AllenCahn.SchwartzResolvent

namespace OAI

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open scoped ContDiff SchwartzMap Polynomial
open Filter Topology

lemma boundedAbove_quadratic_maximum {n : ℕ} {f : Space n → ℝ}
    (hf : Continuous f) {M ε : ℝ} (hb : ∀ x, f x ≤ M) (hε : 0 < ε) :
    ∃ x : Space n, ∀ y, f y-ε*‖y‖^2 ≤ f x-ε*‖x‖^2 := by
  let H : Space n → ℝ := fun x => f x-ε*‖x‖^2
  have hc : Continuous H := by fun_prop
  let R := Real.sqrt ((M-f 0)/ε+1)
  have hR := Real.sqrt_nonneg ((M-f 0)/ε+1)
  have hR2 : R^2 = (M-f 0)/ε+1 := Real.sq_sqrt (by have := hb 0; positivity)
  have hh : ∀ᶠ x in cocompact (Space n), H x ≤ H 0 := by
    filter_upwards [(isCompact_closedBall (0 : Space n) R).compl_mem_cocompact] with x hx
    have hx' : R < ‖x‖ := by
      simpa only [Set.mem_compl_iff,Metric.mem_closedBall,dist_zero_right,not_le] using hx
    have hsq : (M-f 0)/ε+1 < ‖x‖^2 := by nlinarith [norm_nonneg x]
    have hmul := mul_lt_mul_of_pos_left hsq hε
    have he : ε*((M-f 0)/ε+1)=M-f 0+ε := by field_simp
    rw [he] at hmul
    dsimp [H]
    simp only [norm_zero,zero_pow two_ne_zero,mul_zero,sub_zero]
    linarith [hb x]
  exact hc.exists_forall_ge' 0 hh

lemma boundedAbove_maximum_principle {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) {M : ℝ} (hb : ∀ x, f x ≤ M)
    (hpde : ∀ x, 0 < f x → f x ≤ Laplacian.laplacian f x) : ∀ x, f x ≤ 0 := by
  intro x₀
  by_contra hbad
  have hpos : 0 < f x₀ := lt_of_not_ge hbad
  have hn : ∀ᶠ t : ℝ in 𝓝 0,
      2*n*t < f x₀/2 ∧ t*‖x₀‖^2 < f x₀/2 := by
    apply Filter.Eventually.and
    · exact (isOpen_lt (continuous_const.mul continuous_id) continuous_const).mem_nhds
        (by simpa using half_pos hpos)
    · exact (isOpen_lt (continuous_id.mul continuous_const) continuous_const).mem_nhds
        (by simpa using half_pos hpos)
  obtain ⟨ε,hε,he,hgap⟩ := (frequently_gt_nhds (0 : ℝ)).and_eventually hn |>.exists
  obtain ⟨x,hm⟩ := boundedAbove_quadratic_maximum hf.continuous hb hε
  have hfx : f x₀/2 < f x := by
    have hh := hm x₀
    nlinarith [mul_nonneg hε.le (sq_nonneg ‖x‖)]
  have hp := hpde x (lt_trans (half_pos hpos) hfx)
  have hnorm : ContDiff ℝ 2 (fun z : Space n => ‖z‖^2) := contDiff_id.norm_sq ℝ
  have hF := hf.sub ((contDiff_const : ContDiff ℝ 2 (fun _ : Space n => ε)).mul hnorm)
  have hm' : IsLocalMax (fun z : Space n => f z-ε*‖z‖^2) x := .of_forall hm
  have hl := laplacian_nonpos_of_local_max hF hm'
  rw [laplacian_fun_sub hf (contDiff_const.mul hnorm),laplacian_fun_const_mul hnorm,
    laplacian_norm_sq] at hl
  linarith

lemma boundedAbove_elliptic_comparison {n : ℕ} {u F P : Space n → ℝ}
    (hu : ContDiff ℝ 2 u) (hF : ContDiff ℝ 2 F) {M : ℝ}
    (hb : ∀ x, u x-F x ≤ M) (hP : ∀ x, 1 ≤ P x)
    (he : ∀ x, -Laplacian.laplacian u x+P x*u x ≤ -Laplacian.laplacian F x+P x*F x) :
    ∀ x, u x ≤ F x := by
  have hh := boundedAbove_maximum_principle (hu.sub hF) hb (fun x hx => ?_)
  · intro x
    exact sub_nonpos.mp (hh x)
  · rw [laplacian_fun_sub hu hF]
    have hp := mul_le_mul_of_nonneg_right (hP x) hx.le
    nlinarith [he x]

lemma polynomial_profile_iteratedDeriv (p : Polynomial ℝ) (k : ℕ) :
    ∃ q : Polynomial ℝ, iteratedDeriv k (fun s => p.eval (profile s)) = fun s => q.eval (profile s) := by
  induction k with
  | zero => exact ⟨p,rfl⟩
  | succ k ih =>
    obtain ⟨q,hq⟩ := ih
    refine ⟨q.derivative*(Polynomial.C ((Real.sqrt 2)⁻¹)*(1-Polynomial.X^2)), ?_⟩
    rw [iteratedDeriv_succ,hq]
    funext s
    have HH := (q.hasDerivAt (profile s)).comp s (profile_hasDerivAt s)
    change deriv ((fun y => q.eval y) ∘ profile) s = _
    rw [HH.deriv]
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_sub,
      Polynomial.eval_one,Polynomial.eval_pow,Polynomial.eval_X,profileWeight,div_eq_mul_inv]
    ring

lemma profile_temperate : profile.HasTemperateGrowth := by
  refine ⟨profile_contDiff,fun k => ?_⟩
  obtain ⟨q,hq⟩ := polynomial_profile_iteratedDeriv Polynomial.X k
  have he : iteratedDeriv k profile = fun s => q.eval (profile s) := by simpa using hq
  obtain ⟨z,hz,hm⟩ := isCompact_Icc.exists_isMaxOn
    (show (Set.Icc (-1 : ℝ) 1).Nonempty from ⟨0,by norm_num⟩) q.continuous.abs.continuousOn
  refine ⟨0,|q.eval z|,fun x => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,he,Real.norm_eq_abs,pow_zero,mul_one]
  apply hm
  exact ⟨(Real.neg_one_lt_tanh _).le,(Real.tanh_lt_one _).le⟩

lemma profileWeight_temperate : profileWeight.HasTemperateGrowth :=
  (Function.HasTemperateGrowth.const (1 : ℝ)).sub (profile_temperate.pow 2)

lemma profileWeight_le_one (s : ℝ) : profileWeight s ≤ 1 := by
  dsimp [profileWeight]
  nlinarith [sq_nonneg (profile s)]

def realResolvent {n : ℕ} (f : 𝓢(Space n,ℝ)) : 𝓢(Space n,ℝ) :=
  Classical.choose (EllipticResolvent.exists_real_schwartz_resolvent f)

lemma realResolvent_equation {n : ℕ} (f : 𝓢(Space n,ℝ)) (x : Space n) :
    2*realResolvent f x-Laplacian.laplacian (realResolvent f : Space n → ℝ) x=f x :=
  Classical.choose_spec (EllipticResolvent.exists_real_schwartz_resolvent f) x

lemma schwartz_bounded {n : ℕ} (f : 𝓢(Space n,ℝ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |f x| ≤ M :=
  ⟨SchwartzMap.seminorm ℝ 0 0 f,apply_nonneg _ _,SchwartzMap.norm_le_seminorm ℝ f⟩

lemma realResolvent_nonneg {n : ℕ} {f : 𝓢(Space n,ℝ)} (hf : ∀ x, 0 ≤ f x) :
    ∀ x, 0 ≤ realResolvent f x := by
  obtain ⟨M,hM,hb⟩ := schwartz_bounded (realResolvent f)
  apply boundedAbove_elliptic_comparison (u := fun _ => 0) (F := (realResolvent f : Space n → ℝ))
    contDiff_const ((realResolvent f).smooth 2) (M := M) (P := fun _ => 2)
  · intro x
    linarith [(abs_le.mp (hb x)).1]
  · intro x; norm_num
  · intro x
    simpa only [InnerProductSpace.laplacian_const,Pi.zero_apply,neg_zero,mul_zero,add_zero]
      using (show (0 : ℝ) ≤ -Laplacian.laplacian (realResolvent f : Space n → ℝ) x+2*realResolvent f x by
        linarith [realResolvent_equation f x,hf x])

lemma realResolvent_bound {n : ℕ} {f : 𝓢(Space n,ℝ)} {M : ℝ}
    (hf : ∀ x, |f x| ≤ M) : ∀ x, |realResolvent f x| ≤ M/2 := by
  obtain ⟨B,hB,hb⟩ := schwartz_bounded (realResolvent f)
  have hh (e : ℝ) (he : |e|=1) : ∀ x, e*realResolvent f x ≤ M/2 := by
    apply boundedAbove_elliptic_comparison (u := fun x => e*realResolvent f x)
      (F := fun _ => M/2) (contDiff_const.mul ((realResolvent f).smooth 2)) contDiff_const
      (M := B+|M/2|) (P := fun _ => 2)
    · intro x
      have hmul : |e*realResolvent f x| ≤ B := by rw [abs_mul,he,one_mul]; exact hb x
      linarith [(abs_le.mp hmul).2,le_abs_self (M/2),neg_abs_le (M/2)]
    · intro x; norm_num
    · intro x
      rw [laplacian_fun_const_mul ((realResolvent f).smooth 2)]
      have heq := congrArg (fun r : ℝ => e*r) (realResolvent_equation f x)
      have hmul : |e*f x| ≤ M := by rw [abs_mul,he,one_mul]; exact hf x
      simp only [InnerProductSpace.laplacian_const,Pi.zero_apply,neg_zero,zero_add]
      nlinarith [(abs_le.mp hmul).2]
  intro x
  have h1 := hh 1 (by norm_num) x
  have h2 := hh (-1) (by norm_num) x
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end DeGiorgi
end

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open scoped ContDiff SchwartzMap LineDeriv
open Filter Topology

lemma realResolvent_mono {n : ℕ} {f g : 𝓢(Space n,ℝ)} (h : ∀ x, f x ≤ g x) :
    ∀ x, realResolvent f x ≤ realResolvent g x := by
  obtain ⟨M,hM,hMb⟩ := schwartz_bounded (realResolvent f)
  obtain ⟨N,hN,hNb⟩ := schwartz_bounded (realResolvent g)
  apply boundedAbove_elliptic_comparison ((realResolvent f).smooth 2)
    ((realResolvent g).smooth 2) (M := M+N) (P := fun _ => 2)
  · intro x
    linarith [(abs_le.mp (hMb x)).2,(abs_le.mp (hNb x)).1]
  · intro x; norm_num
  · intro x
    linarith [realResolvent_equation f x,realResolvent_equation g x,h x]

lemma realResolvent_comparison {n : ℕ} {f : 𝓢(Space n,ℝ)} {F : Space n → ℝ}
    (hF : ContDiff ℝ 2 F) (hp : ∀ x, 0 ≤ F x)
    (he : ∀ x, f x ≤ 2*F x-Laplacian.laplacian F x) :
    ∀ x, realResolvent f x ≤ F x := by
  obtain ⟨M,hM,hb⟩ := schwartz_bounded (realResolvent f)
  apply boundedAbove_elliptic_comparison ((realResolvent f).smooth 2) hF
    (M := M) (P := fun _ => 2)
  · intro x; linarith [(abs_le.mp (hb x)).2,hp x]
  · intro x; norm_num
  · intro x; linarith [realResolvent_equation f x,he x]

lemma realResolvent_isometry {n : ℕ} (f : 𝓢(Space n,ℝ))
    (J : Space n ≃ₗᵢ[ℝ] Space n) (hJ : ∀ x, f (J x)=f x) :
    ∀ x, realResolvent f (J x)=realResolvent f x := by
  let u := realResolvent f
  have hu : ContDiff ℝ 2 (fun x => u (J x)) := (u.smooth 2).comp J.contDiff
  obtain ⟨M,hM,hb⟩ := schwartz_bounded u
  have hEq (x) : 2*u (J x)-Laplacian.laplacian (fun x => u (J x)) x=f x := by
    rw [PoissonSupport.DeGiorgi.laplacian_comp_isometry (u.smooth 2)]
    exact (realResolvent_equation f (J x)).trans (hJ x)
  have h₁ : ∀ x, u (J x) ≤ u x := by
    apply boundedAbove_elliptic_comparison hu (u.smooth 2) (M := 2*M) (P := fun _ => 2)
    · intro x; linarith [(abs_le.mp (hb x)).1,(abs_le.mp (hb (J x))).2]
    · intro x; norm_num
    · intro x; linarith [hEq x,realResolvent_equation f x]
  have h₂ : ∀ x, u x ≤ u (J x) := by
    apply boundedAbove_elliptic_comparison (u.smooth 2) hu (M := 2*M) (P := fun _ => 2)
    · intro x; linarith [(abs_le.mp (hb x)).2,(abs_le.mp (hb (J x))).1]
    · intro x; norm_num
    · intro x; linarith [hEq x,realResolvent_equation f x]
  exact fun x => le_antisymm (h₁ x) (h₂ x)

lemma schwartz_coordinateJet {n : ℕ} (f : 𝓢(Space n,ℝ)) (l : List (Fin n)) :
    ∃ g : 𝓢(Space n,ℝ), (g : Space n → ℝ)=coordinateJet f l := by
  induction l with
  | nil => exact ⟨f,rfl⟩
  | cons i l ih =>
    obtain ⟨g,hg⟩ := ih
    refine ⟨∂_{basis n i} g, ?_⟩
    funext x
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv,hg]
    rfl

lemma schwartz_jets_bounded {n : ℕ} (f : 𝓢(Space n,ℝ)) (l : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |coordinateJet f l x| ≤ C := by
  obtain ⟨g,hg⟩ := schwartz_coordinateJet f l
  simpa only [hg] using schwartz_bounded g

lemma JetControl.reindex {n : ℕ} {α β : Type*} {S : Set α} {T : Set β}
    {w f : α → Space n → ℝ} {k : ℕ} (h : JetControl S w f k) (g : β → α)
    (hg : ∀ b ∈ T, g b ∈ S) :
    JetControl T (fun b => w (g b)) (fun b => f (g b)) k := by
  intro l hl
  obtain ⟨C,hC,hb⟩ := h l hl
  exact ⟨C,hC,fun b hT x => hb (g b) (hg b hT) x⟩

def resolventIterate {n : ℕ} (V : Space n → ℝ) (f : 𝓢(Space n,ℝ)) : ℕ → 𝓢(Space n,ℝ)
  | 0 => 0
  | k+1 => realResolvent (f+SchwartzMap.smulLeftCLM ℝ V (resolventIterate V f k))

lemma resolventIterate_equation {n : ℕ} {V : Space n → ℝ} (hV : V.HasTemperateGrowth)
    (f : 𝓢(Space n,ℝ)) (k : ℕ) (x : Space n) :
    2*resolventIterate V f (k+1) x-Laplacian.laplacian (resolventIterate V f (k+1) : Space n → ℝ) x =
      f x+V x*resolventIterate V f k x := by
  simpa only [resolventIterate,add_apply,SchwartzMap.smulLeftCLM_apply_apply hV,smul_eq_mul]
    using realResolvent_equation (f+SchwartzMap.smulLeftCLM ℝ V (resolventIterate V f k)) x

lemma resolventIterate_nonneg {n : ℕ} {V : Space n → ℝ} (hV : V.HasTemperateGrowth)
    (hV0 : ∀ x, 0 ≤ V x) {f : 𝓢(Space n,ℝ)} (hf : ∀ x, 0 ≤ f x) :
    ∀ k x, 0 ≤ resolventIterate V f k x := by
  intro k
  induction k with
  | zero => simp [resolventIterate]
  | succ k ih =>
    apply realResolvent_nonneg
    intro x
    simpa only [add_apply,SchwartzMap.smulLeftCLM_apply_apply hV,smul_eq_mul]
      using add_nonneg (hf x) (mul_nonneg (hV0 x) (ih x))

lemma resolventIterate_comparison {n : ℕ} {V F : Space n → ℝ}
    (hV : V.HasTemperateGrowth) (hV0 : ∀ x, 0 ≤ V x)
    (hF : ContDiff ℝ 2 F) (hF0 : ∀ x, 0 ≤ F x) {f : 𝓢(Space n,ℝ)}
    (he : ∀ x, f x+V x*F x ≤ 2*F x-Laplacian.laplacian F x) :
    ∀ k x, resolventIterate V f k x ≤ F x := by
  intro k
  induction k with
  | zero => simpa [resolventIterate] using hF0
  | succ k ih =>
    apply realResolvent_comparison hF hF0
    intro x
    simp only [add_apply,SchwartzMap.smulLeftCLM_apply_apply hV,smul_eq_mul]
    exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left (ih x) (hV0 x))).trans (he x)

lemma resolventIterate_mono_source {n : ℕ} {V : Space n → ℝ}
    (hV : V.HasTemperateGrowth) (hV0 : ∀ x, 0 ≤ V x) {f g : 𝓢(Space n,ℝ)}
    (hfg : ∀ x, f x ≤ g x) : ∀ k x, resolventIterate V f k x ≤ resolventIterate V g k x := by
  intro k
  induction k with
  | zero => simp only [resolventIterate,le_refl,implies_true]
  | succ k ih =>
    apply realResolvent_mono
    intro x
    simp only [add_apply,SchwartzMap.smulLeftCLM_apply_apply hV,smul_eq_mul]
    exact add_le_add (hfg x) (mul_le_mul_of_nonneg_left (ih x) (hV0 x))

lemma resolventIterate_mono_index {n : ℕ} {V : Space n → ℝ}
    (hV : V.HasTemperateGrowth) (hV0 : ∀ x, 0 ≤ V x) {f : 𝓢(Space n,ℝ)}
    (hf : ∀ x, 0 ≤ f x) (x : Space n) : Monotone (fun k => resolventIterate V f k x) := by
  apply monotone_nat_of_le_succ
  have H : ∀ k x, resolventIterate V f k x ≤ resolventIterate V f (k+1) x := by
    intro k
    induction k with
    | zero => simpa only [resolventIterate,zero_apply] using resolventIterate_nonneg hV hV0 hf 1
    | succ k ih =>
      apply realResolvent_mono
      intro x
      simp only [add_apply,SchwartzMap.smulLeftCLM_apply_apply hV,smul_eq_mul]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (ih x) (hV0 x))
  exact fun k => H k x

lemma resolventIterate_isometry {n : ℕ} {V : Space n → ℝ} (hV : V.HasTemperateGrowth)
    (J : Space n ≃ₗᵢ[ℝ] Space n) {f : 𝓢(Space n,ℝ)}
    (hJV : ∀ x, V (J x)=V x) (hJf : ∀ x, f (J x)=f x) :
    ∀ k x, resolventIterate V f k (J x)=resolventIterate V f k x := by
  intro k
  induction k with
  | zero => simp [resolventIterate]
  | succ k ih =>
    apply realResolvent_isometry _ J
    intro x
    simp only [add_apply,SchwartzMap.smulLeftCLM_apply_apply hV,smul_eq_mul,hJV,hJf,ih]

end DeGiorgi
end

end OAI
