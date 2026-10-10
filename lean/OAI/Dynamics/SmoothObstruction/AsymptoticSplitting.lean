import OAI.Dynamics.SmoothObstruction.SplittingStability
import OAI.Dynamics.SmoothObstruction.SmoothScales

namespace OAI

section

open Filter Topology
open scoped Real

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability RelativeProduct
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

lemma segment_toEuclidean (A : ℕ → Matrix (Fin d) (Fin d) ℝ) (s l : ℕ) :
    segment (fun t => Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (A t)) s l =
      Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (propagator A s l) := by
  induction l with
  | zero => simp [RelativeProduct.segment, propagator]
  | succ l ih => simp only [segment_succ, propagator, ih, map_mul]

/-- No product bounds are assumed: every interval follows from the actual
coordinate derivative equations and the uniformly bounded finite gauges. -/
theorem actual_interval_exterior
    (A U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (S : Finset (Fin d)) (N : ℕ) {γ g K C : ℝ}
    (hUV : ∀ t, U t * V t = 1) (hVU : ∀ t, V t * U t = 1)
    (hA : ∀ t < N, A t * U t = U (t+1) * rate lam 1)
    (hg : 0 ≤ g) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hfast : ∀ j ∈ S, γ + g ≤ lam j) (hslow : ∀ j ∉ S, lam j ≤ γ - g)
    (hU : ∀ t ≤ N, ‖U t‖ ≤ Real.exp K) (hV : ∀ t ≤ N, ‖V t‖ ≤ Real.exp K)
    (hpoly : ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior S.card A‖ ≤ C * (max 1 ‖A‖)^S.card)
    (s l : ℕ) (hsl : s + l ≤ N) :
    ‖exterior S.card (segment (fun t => Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (A t)) s l)‖ ≤
      C^2 * (Real.exp K)^(2*S.card) * (Fintype.card (powersetCard (Fin d) S.card) : ℝ) *
        Real.exp ((∑ j ∈ S, lam j) * l) := by
  rw [segment_toEuclidean, propagator_eq_transition A U V lam hUV hVU N hA s l hsl]
  convert transition_exterior_bound U V lam S (by omega : s ≤ s+l)
    hg hK hC hfast hslow (hU _ hsl) (hV _ (by omega)) hpoly using 1
  congr 2
  push_cast
  ring

lemma absorb_prefactor {C R H K D z : ℝ} {p d : ℕ}
    (_hC : 0 ≤ C) (_hR : 0 ≤ R) (hRH : R ≤ H) (hH : 0 ≤ H)
    (hp : p ≤ d) (hD : 0 ≤ D) (hz : 1 ≤ z) (hK : K ≤ D*z) :
    C^2 * (Real.exp K)^(2*p) * R ≤ Real.exp ((C^2*H + 2*d*D)*z) := by
  have hz0 : 0 ≤ z := by linarith
  have hKR : (2*p:ℕ)*K ≤ (2*d:ℕ)*D*z := by
    have hp' : (p:ℝ) ≤ d := by exact_mod_cast hp
    have h₁ := mul_le_mul_of_nonneg_left hK (show 0 ≤ ((2*p:ℕ):ℝ) by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hp' (mul_nonneg hD hz0)
    push_cast at h₁ ⊢
    nlinarith
  have hconst : C^2 * R ≤ Real.exp (C^2*H*z) := by
    calc
      _ ≤ C^2*H := mul_le_mul_of_nonneg_left hRH (sq_nonneg _)
      _ ≤ C^2*H*z := le_mul_of_one_le_right (by positivity) hz
      _ ≤ _ := (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  calc
    _ = (C^2*R) * Real.exp ((2*p:ℕ)*K) := by rw [Real.exp_nat_mul]; ring
    _ ≤ Real.exp (C^2*H*z) * Real.exp ((2*d:ℕ)*D*z) :=
      mul_le_mul hconst (Real.exp_le_exp.mpr hKR) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

/-- One exponential constant works for every possible fast rank, including
zero. Dimension dependent polynomial norms and gauge prefactors are derived,
not added as assumptions about the derivative cocycle. -/
theorem exists_uniform_interval_constant (d : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (A U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
      (lam : Fin d → ℝ) (S : Finset (Fin d)) (N : ℕ) (γ g K z : ℝ),
      1 ≤ z → 0 ≤ g → 0 ≤ K → K ≤ D*z →
      (∀ t, U t * V t = 1) → (∀ t, V t * U t = 1) →
      (∀ t < N, A t * U t = U (t+1) * rate lam 1) →
      (∀ j ∈ S, γ+g ≤ lam j) → (∀ j ∉ S, lam j ≤ γ-g) →
      (∀ t ≤ N, ‖U t‖ ≤ Real.exp K) → (∀ t ≤ N, ‖V t‖ ≤ Real.exp K) →
      ∀ s l : ℕ, s+l ≤ N →
        ‖exterior S.card (segment (fun t => Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (A t)) s l)‖ ≤
          Real.exp ((∑ j ∈ S, lam j)*l + C₁*z) := by
  choose C hC hpoly using fun p : Fin (d+1) =>
    exists_power_bound (E:=EuclideanSpace ℝ (Fin d)) p.val
  let C' : ℝ := ∑ p, C p
  let H : ℝ := ∑ p : Fin (d+1), (Fintype.card (powersetCard (Fin d) p.val) : ℝ)
  have hC0 (p : Fin (d+1)) : 0 ≤ C p := le_trans zero_le_one (hC p)
  have hC' : 0 ≤ C' := Finset.sum_nonneg fun p _ => hC0 p
  have hH : 0 ≤ H := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  refine ⟨C'^2*H + 2*d*D, by positivity, ?_⟩
  intro A U V lam S N γ g K z hz hg hK hKD hUV hVU hA hf hs hU hV s l hsl
  have hp : S.card ≤ d := by simpa using S.card_le_univ
  let p : Fin (d+1) := ⟨S.card, by omega⟩
  have hCp : C p ≤ C' := Finset.single_le_sum (fun q _ => hC0 q) (Finset.mem_univ p)
  have hHp : (Fintype.card (powersetCard (Fin d) S.card):ℝ) ≤ H :=
    by
    change (Fintype.card (powersetCard (Fin d) p.val):ℝ) ≤
      ∑ q : Fin (d+1), (Fintype.card (powersetCard (Fin d) q.val):ℝ)
    exact Finset.single_le_sum
      (f:=fun q : Fin (d+1) => (Fintype.card (powersetCard (Fin d) q.val):ℝ))
      (fun q _ => Nat.cast_nonneg _) (Finset.mem_univ p)
  have hpower : ∀ T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖exterior S.card T‖ ≤ C' * (max 1 ‖T‖)^S.card := fun T =>
    (hpoly p T).trans (mul_le_mul_of_nonneg_right hCp (pow_nonneg (by positivity) _))
  calc
    _ ≤ C'^2 * (Real.exp K)^(2*S.card) * (Fintype.card (powersetCard (Fin d) S.card):ℝ) *
        Real.exp ((∑ j ∈ S, lam j)*l) :=
      actual_interval_exterior A U V lam S N hUV hVU hA hg hK hC' hf hs hU hV hpower s l hsl
    _ ≤ Real.exp ((C'^2*H + 2*d*D)*z) * Real.exp ((∑ j ∈ S, lam j)*l) :=
      mul_le_mul_of_nonneg_right (absorb_prefactor hC' (Nat.cast_nonneg _) hHp hH hp hD hz hKD)
        (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.EuclideanSplitting
open ExteriorStability RelativeProduct
open scoped Matrix.Norms.L2Operator

lemma rate_sum_abs_le {d : ℕ} (lam : Fin d → ℝ) (S : Finset (Fin d))
    {R : ℝ} (hR : 0 ≤ R) (hlam : ∀ i, |lam i| ≤ R) :
    |∑ i ∈ S, lam i| ≤ d * R := by
  calc
    _ ≤ ∑ i ∈ S, |lam i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ S, R := Finset.sum_le_sum fun i _ => hlam i
    _ = S.card * R := by simp
    _ ≤ d * R := mul_le_mul_of_nonneg_right (by exact_mod_cast (show S.card ≤ d by simpa using S.card_le_univ)) hR

/-- Choice-independent relative stability on ALL actual gauged intervals
at once. The only perturbation hypothesis is the genuine one-step derivative
error; all subinterval exterior bounds are proved from the gauge equations.
The same numerical envelope works for every fast rank and every witness. -/
theorem uniform_relative_gauged (d : ℕ) (K₀ D : ℝ) (hD : 0 ≤ D) :
    ∃ C C₁ : ℝ, 0 ≤ C ∧ 0 ≤ C₁ ∧
      ∀ (A U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
        (T : ℕ → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
        (lam : Fin d → ℝ) (S : Finset (Fin d)) (m : ℕ)
        (γ g K b n C₀ R C₃ ε : ℝ),
        0 ≤ b → 0 ≤ n → 1 ≤ b*n → 0 ≤ C₀ → 0 ≤ R → 0 ≤ C₃ →
        0 ≤ g → 0 ≤ K → K ≤ D*(b*n) → (m:ℝ) ≤ 2*n →
        (∀ t, U t*V t=1) → (∀ t,V t*U t=1) →
        (∀ t < m,A t*U t=U (t+1)*rate lam 1) →
        (∀ i,|lam i| ≤ R) →
        (∀ j ∈ S, γ+g ≤ lam j) → (∀ j ∉ S, lam j ≤ γ-g) →
        (∀ t ≤ m, ‖U t‖ ≤ Real.exp K) → (∀ t ≤ m, ‖V t‖ ≤ Real.exp K) →
        0 ≤ ε → ε ≤ 1 → ε ≤ C₃*Real.exp (-(3/2:ℝ)*SmoothScales.B b*n) →
        (∀ t < m, ‖A t‖ ≤ K₀) →
        (∀ t < m, ‖T t-Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (A t)‖ ≤ ε) →
        ‖exterior S.card (segment T 0 m) -
          exterior S.card (segment (fun t => Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (A t)) 0 m)‖ /
            Real.exp ((∑ j ∈ S,lam j)*m-C₀*b*n) ≤
          RelativeAsymptotics.envelope C C₀ C₁ (d*R) C₃ b n *
            Real.exp (RelativeAsymptotics.envelope C C₀ C₁ (d*R) C₃ b n) := by
  obtain ⟨C,hC,hrel⟩ := relative_exterior_core (E:=EuclideanSpace ℝ (Fin d)) d K₀
  obtain ⟨C₁,hC₁,hinterval⟩ := exists_uniform_interval_constant d D hD
  refine ⟨C,C₁,hC,hC₁,?_⟩
  intro A U V T lam S m γ g K b n C₀ R C₃ ε hb hn hbn hC₀ hR hC₃
    hg hK hKD hm hUV hVU hA hlam hf hs hU hV hε hε₁ hεle hnorm hnear
  have hseg := hinterval A U V lam S m γ g K (b*n) hbn hg hK hKD hUV hVU hA hf hs hU hV
  have hp : S.card ≤ d := by simpa using S.card_le_univ
  have hbound := hrel S.card hp
    (fun t => Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (A t)) T m
    (∑ j ∈ S,lam j) (C₁*(b*n)) ε hε hε₁
    (fun t ht => by simpa only [Matrix.l2_opNorm_toEuclideanCLM] using hnorm t ht) hnear hseg
  exact RelativeAsymptotics.uniform_relative_bound _ _ _ _ b n C C₀ C₁ (d*R) C₃ m
    hb hn hC hC₀ hC₃ (by positivity) hε hm (by ring_nf; rfl)
    (rate_sum_abs_le lam S hR hlam) hεle hbound
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.EuclideanSplitting
open Set ExteriorStability RelativeProduct ShortDerivative
open scoped Matrix.Norms.L2Operator

/-- The uniform, all-rank, choice-independent relative error for derivatives
of actual nonlinear orbit compositions. All interval bounds are derived from
the genuine gauge equations, and the perturbations from the one-step C²
bounds and the orbit tube. No long-iterate regularity bound is assumed. -/
theorem actual_uniform_relative (d : ℕ) (K₀ Dg : ℝ) (hDg : 0 ≤ Dg) :
    ∃ C C₁ : ℝ, 0 ≤ C ∧ 0 ≤ C₁ ∧
      ∀ (f : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (x y : ℕ → EuclideanSpace ℝ (Fin d)) (s : ℕ → Set (EuclideanSpace ℝ (Fin d)))
        (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
        (S : Finset (Fin d)) (m : ℕ) (γ g K b n C₀ R D : ℝ),
        0 ≤ b → 0 ≤ n → 1 ≤ b*n → 0 ≤ C₀ → 0 ≤ R → 0 ≤ D →
        0 ≤ g → 0 ≤ K → K ≤ Dg*(b*n) → (m:ℝ) ≤ 2*n →
        (∀ t, U t*V t=1) → (∀ t,V t*U t=1) →
        (∀ t < m, (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
          (fderiv ℝ (f t) (x t))*U t=U (t+1)*rate lam 1) →
        (∀ i,|lam i| ≤ R) →
        (∀ j ∈ S, γ+g ≤ lam j) → (∀ j ∉ S, lam j ≤ γ-g) →
        (∀ t ≤ m, ‖U t‖ ≤ Real.exp K) → (∀ t ≤ m, ‖V t‖ ≤ Real.exp K) →
        D*Real.exp (-(3/2:ℝ)*SmoothScales.B b*n) ≤ 1 →
        (∀ t < m, f t (x t)=x (t+1) ∧ f t (y t)=y (t+1)) →
        (∀ t < m, x t∈s t ∧ y t∈s t ∧ Convex ℝ (s t) ∧
          (∀ z∈s t,DifferentiableAt ℝ (f t) z) ∧
          (∀ z∈s t,DifferentiableAt ℝ (fderiv ℝ (f t)) z) ∧
          (∀ z∈s t,‖fderiv ℝ (f t) z‖≤K₀) ∧
          (∀ z∈s t,‖fderiv ℝ (fderiv ℝ (f t)) z‖≤D)) →
        (∀ t < m,‖y t-x t‖≤Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)) →
        ‖exterior S.card (fderiv ℝ (iterate f m) (y 0)) -
          exterior S.card (fderiv ℝ (iterate f m) (x 0))‖ /
            Real.exp ((∑ j ∈ S,lam j)*m-C₀*b*n) ≤
          RelativeAsymptotics.envelope C C₀ C₁ (d*R) D b n *
            Real.exp (RelativeAsymptotics.envelope C C₀ C₁ (d*R) D b n) := by
  obtain ⟨C,C₁,hC,hC₁,hh⟩ := uniform_relative_gauged d K₀ Dg hDg
  refine ⟨C,C₁,hC,hC₁,?_⟩
  intro f x y s U V lam S m γ g K b n C₀ R D hb hn hbn hC₀ hR hD
    hg hK hKD hm hUV hVU hA hlam hf hs hU hV hε horbit hpatch hshadow
  let A := fun t => (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm (fderiv ℝ (f t) (x t))
  let T := fun t => fderiv ℝ (f t) (y t)
  have he (t : ℕ) : Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (A t)=fderiv ℝ (f t) (x t) := by
    exact (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).apply_symm_apply _
  have hnorm (t : ℕ) (ht : t < m) : ‖A t‖≤K₀ := by
    rw [←Matrix.l2_opNorm_toEuclideanCLM,he]
    exact (hpatch t ht).2.2.2.2.2.1 _ (hpatch t ht).1
  have hnear (t : ℕ) (ht : t < m) : ‖T t-Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (A t)‖≤
      D*Real.exp (-(3/2:ℝ)*SmoothScales.B b*n) := by
    rw [he]
    obtain ⟨hx,hy,hconv,hf,hff,_,hsecond⟩ := hpatch t ht
    exact (hconv.norm_image_sub_le_of_norm_fderiv_le hff hsecond hx hy).trans
      (mul_le_mul_of_nonneg_left (hshadow t ht) hD)
  have hbound := hh A U V T lam S m γ g K b n C₀ R D
    (D*Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)) hb hn hbn hC₀ hR hD hg hK hKD hm
    hUV hVU hA hlam hf hs hU hV (by positivity) hε le_rfl hnorm hnear
  have hx := derivative_iterate f x
    (fun t => Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (A t)) m (fun t ht => (horbit t ht).1)
    (fun t ht => by rw [he]; exact ((hpatch t ht).2.2.2.1 _ (hpatch t ht).1).hasFDerivAt)
  have hy := derivative_iterate f y T m (fun t ht => (horbit t ht).2)
    (fun t ht => ((hpatch t ht).2.2.2.1 _ (hpatch t ht).2.1).hasFDerivAt)
  rwa [←hx.fderiv,←hy.fderiv] at hbound
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The nonautonomous chart composition has exactly the same germ as the
actual long iterate in the two endpoint charts. Intermediate chart codes
therefore never have to be encoded in the partition or switch labels. -/
theorem iterate_localMap_germ (S : Diffeomorph I I M M ∞) (a : ℕ → M) (x : M)
    (N : ℕ) (hx : ∀ t≤N,(S^[t]) x∈(extChartAt I (a t)).source)
    (hint : (extChartAt I (a 0)) x∈interior (range I)) :
    ShortDerivative.iterate (fun t => localMap I S (a t) (a (t+1))) N =ᶠ[𝓝 ((extChartAt I (a 0)) x)]
      extChartAt I (a N) ∘ S^[N] ∘ (extChartAt I (a 0)).symm := by
  have hx0 : x∈(extChartAt I (a 0)).source := hx 0 (Nat.zero_le _)
  induction N with
  | zero =>
    have ht := extChartAt_target_mem_nhdsWithin' hx0
    rw [nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp hint)] at ht
    filter_upwards [ht] with u hu
    exact ((extChartAt I (a 0)).right_inv hu).symm
  | succ N ih =>
    have hi := ih (fun t ht => hx t (by omega))
    have hc : ContinuousAt (S^[N] ∘ (extChartAt I (a 0)).symm) ((extChartAt I (a 0)) x) :=
      (S.continuous.iterate N).continuousAt.comp (continuousAt_extChartAt_symm' hx0)
    have hs : ∀ᶠ u in 𝓝 ((extChartAt I (a 0)) x),
        (S^[N]) ((extChartAt I (a 0)).symm u)∈(extChartAt I (a N)).source := by
      apply hc.preimage_mem_nhds
      apply (isOpen_extChartAt_source (I := I) (a N)).mem_nhds
      simpa only [Function.comp_apply,(extChartAt I (a 0)).left_inv hx0] using hx N (by omega)
    filter_upwards [hi,hs] with u hu hsu
    change (extChartAt I (a (N+1))) (S ((extChartAt I (a N)).symm
      (ShortDerivative.iterate (fun t => localMap I S (a t) (a (t+1))) N u))) = _
    rw [hu]
    simp only [Function.comp_apply,(extChartAt I (a N)).left_inv hsu,Function.iterate_succ_apply']
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology Metric EuclideanSplitting ExteriorStability ShortDerivative
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- The relative exterior estimate for the ACTUAL long iterate, in the old
input's endpoint charts. The constants are uniform over all ranks, rates,
gauges and selectors. The tube condition is imposed on the genuine new orbit;
no assumed derivative or determinant estimate is used. -/
theorem actual_endpoint_relative (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (L : ι → Set M)
    (hL : ∀ i,IsCompact (L i)) (hLU : ∀ i,L i⊆(chartAt H (a i)).source)
    (Dg : ℝ) (hDg : 0≤Dg) :
    ∃ r K₀ C C₁ : ℝ,0<r ∧ 1≤K₀ ∧ 0≤C ∧ 0≤C₁ ∧
      ∀ (c : M → ι) (x y : M) (m : ℕ)
        (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
        (T : Finset (Fin d)) (γ g K b n C₀ R : ℝ),
        (∀ z,z∈L (c z)) → 0≤b → 0≤n → 1≤b*n → 0≤C₀ → 0≤R →
        0≤g → 0≤K → K≤Dg*(b*n) → (m:ℝ)≤2*n →
        (∀ t,U t*V t=1) → (∀ t,V t*U t=1) →
        (∀ t < m,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
          (coord I S (a (c (S^[t] x))) (a (c (S^[t+1] x))) (S^[t] x))*U t=
            U (t+1)*rate lam 1) →
        (∀ i,|lam i|≤R) → (∀ j∈T,γ+g≤lam j) → (∀ j∉T,lam j≤γ-g) →
        (∀ t ≤ m,‖U t‖≤Real.exp K) → (∀ t ≤ m,‖V t‖≤Real.exp K) →
        K₀*Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)≤1 →
        Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)≤r →
        (∀ t ≤ m,(S^[t]) y∈(extChartAt I (a (c (S^[t] x)))).source) →
        (∀ t ≤ m,‖(extChartAt I (a (c (S^[t] x)))) (S^[t] y)-
          (extChartAt I (a (c (S^[t] x)))) (S^[t] x)‖≤
            Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)) →
        (∀ t ≤ m,closedBall ((extChartAt I (a (c (S^[t] x)))) (S^[t] x))
          (Real.exp (-(3/2:ℝ)*SmoothScales.B b*n))⊆interior (range I)) →
        let F := extChartAt I (a (c (S^[m] x))) ∘ S^[m] ∘ (extChartAt I (a (c x))).symm
        let ux := (extChartAt I (a (c x))) x
        let uy := (extChartAt I (a (c x))) y
        ‖exterior T.card (fderiv ℝ F uy)-exterior T.card (fderiv ℝ F ux)‖ /
          Real.exp ((∑ j∈T,lam j)*m-C₀*b*n)≤
            RelativeAsymptotics.envelope C C₀ C₁ (d*R) K₀ b n *
              Real.exp (RelativeAsymptotics.envelope C C₀ C₁ (d*R) K₀ b n) := by
  obtain ⟨r,K₀,hr,hK₀,hc₂⟩ := actual_uniform_c2 I hclosed S a L hL hLU
  obtain ⟨C,C₁,hC,hC₁,hrel⟩ := actual_uniform_relative d K₀ Dg hDg
  refine ⟨r,K₀,C,C₁,hr,hK₀,hC,hC₁,?_⟩
  intro c x y m U V lam T γ g K b n C₀ R hc hb hn hbn hC₀ hR hg hK hKD hm
    hUV hVU hstep hlam hfast hslow hU hV hε hεr hychart htube hsafe F ux uy
  let ca (t : ℕ) := a (c (S^[t] x))
  let xv (t : ℕ) := (extChartAt I (ca t)) (S^[t] x)
  let yv (t : ℕ) := (extChartAt I (ca t)) (S^[t] y)
  let δ := Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)
  let f (t : ℕ) := localMap I S (ca t) (ca (t+1))
  let s (t : ℕ) := closedBall (xv t) δ
  have hxchart (t : ℕ) : S^[t] x∈(extChartAt I (ca t)).source  := by
    simpa only [extChartAt_source,ca] using hLU (c (S^[t] x)) (hc (S^[t] x))
  have hxc (t : ℕ) : xv t∈s t := mem_closedBall_self (Real.exp_nonneg _)
  have hyc (t : ℕ) (ht : t ≤ m) : yv t∈s t := by
    exact mem_closedBall.mpr (by simpa only [dist_eq_norm] using htube t ht)
  have hreg (t : ℕ) (ht : t < m) (z : EuclideanSpace ℝ (Fin d)) (hz : z∈s t) :
      ContDiffAt ℝ ∞ (f t) z ∧ ‖fderiv ℝ (f t) z‖≤K₀ ∧
        ‖fderiv ℝ (fderiv ℝ (f t)) z‖≤K₀ := by
    have hh := hc₂ (c (S^[t] x)) (c (S^[t+1] x)) (S^[t] x) (hc _)
      (by simpa only [Function.iterate_succ_apply'] using hc (S^[t+1] x))
    exact hh.2 z (closedBall_subset_closedBall hεr hz) (hsafe t ht.le hz)
  have hstep' (t : ℕ) (ht : t < m) :
      (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm (fderiv ℝ (f t) (xv t))*U t=
        U (t+1)*rate lam 1 := by
    have hsrc : S (S^[t] x)∈(chartAt H (ca (t+1))).source := by
      simpa only [extChartAt_source,Function.iterate_succ_apply'] using hxchart (t+1)
    have hd := hasFDerivAt_localMap I S (ca t) (ca (t+1)) (S^[t] x)
      ⟨by simpa only [extChartAt_source] using hxchart t,hsrc⟩ (hsafe t ht.le (hxc t))
    rw [show fderiv ℝ (f t) (xv t)=coord I S (ca t) (ca (t+1)) (S^[t] x) from hd.fderiv]
    exact hstep t ht
  have horbit (t : ℕ) (ht : t < m) : f t (xv t)=xv (t+1) ∧ f t (yv t)=yv (t+1) := by
    simp only [f,localMap,Function.comp_apply,xv,yv,
      (extChartAt I (ca t)).left_inv (hxchart t),
      (extChartAt I (ca t)).left_inv (hychart t ht.le),Function.iterate_succ_apply']
    trivial
  have he := hrel f xv yv s U V lam T m γ g K b n C₀ R K₀ hb hn hbn hC₀ hR
    (by linarith) hg hK hKD hm hUV hVU hstep' hlam hfast hslow hU hV hε horbit
    (fun t ht => ⟨hxc t,hyc t ht.le,convex_closedBall _ _,
      fun z hz => (hreg t ht z hz).1.differentiableAt (by simp),
      fun z hz => ((hreg t ht z hz).1.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp),
      fun z hz => (hreg t ht z hz).2.1,fun z hz => (hreg t ht z hz).2.2⟩)
    (fun t ht => htube t ht.le)
  have egx := iterate_localMap_germ I S ca x m (fun t _ => hxchart t)
    (hsafe 0 (Nat.zero_le _) (hxc 0))
  have egy := iterate_localMap_germ I S ca y m hychart
    (hsafe 0 (Nat.zero_le _) (hyc 0 (Nat.zero_le _)))
  dsimp only [f,xv,yv] at he
  simp only [Function.iterate_zero_apply] at he
  rw [egx.fderiv_eq (𝕜:=ℝ),egy.fderiv_eq (𝕜:=ℝ)] at he
  exact he
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ShortDerivative
open scoped ContDiff Matrix.Norms.L2Operator
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma contDiffAt_iterate (f : ℕ → E → E) (x : ℕ → E) (N : ℕ)
    (hx : ∀ t<N,f t (x t)=x (t+1))
    (hf : ∀ t<N,ContDiffAt ℝ ∞ (f t) (x t)) :
    ContDiffAt ℝ ∞ (iterate f N) (x 0) := by
  induction N with
  | zero => exact contDiffAt_id
  | succ N ih =>
    have hi := ih (fun t ht => hx t (by omega)) (fun t ht => hf t (by omega))
    have he := orbit_eq_iterate f x (N+1) hx N (by omega)
    have hN := hf N (by omega)
    rw [←he] at hN
    exact hN.comp (x 0) hi
end SmoothObstruction.ShortDerivative

namespace SmoothObstruction.EuclideanSplitting
open ShortDerivative RelativeProduct
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A gauge for the actual one-step differentials identifies the derivative
of the true orbit composition with its genuine transition matrix. -/
lemma derivative_transition (f : ℕ → E → E) (x : ℕ → E)
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ) (N : ℕ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (hx : ∀ t<N,f t (x t)=x (t+1))
    (hd : ∀ t<N,DifferentiableAt ℝ (f t) (x t))
    (hstep : ∀ t<N,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
      (fderiv ℝ (f t) (x t))*U t=U (t+1)*rate lam 1) :
    HasFDerivAt (iterate f N)
      (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam 0 N)) (x 0) := by
  let A := fun t => (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm (fderiv ℝ (f t) (x t))
  have he (t : ℕ) : Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (A t)=fderiv ℝ (f t) (x t) :=
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).apply_symm_apply _
  have hh := derivative_iterate f x (fun t => Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (A t))
    N hx (fun t ht => by rw [he]; exact (hd t ht).hasFDerivAt)
  rw [segment_toEuclidean,propagator_eq_transition A U V lam hUV hVU N hstep 0 N (by omega)] at hh
  simpa only [Nat.zero_add] using hh
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology ShortDerivative EuclideanSplitting
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Regularity of the actual endpoint expression in the old charts, not a
formal composition with unrelated derivatives. -/
theorem actual_endpoint_smooth (S : Diffeomorph I I M M ∞) (a : ℕ → M) (x : M) (n : ℕ)
    (hx : ∀ t ≤ n,S^[t] x∈(extChartAt I (a t)).source)
    (hi : ∀ t ≤ n,(extChartAt I (a t)) (S^[t] x)∈interior (range I)) :
    ContDiffAt ℝ ∞ (extChartAt I (a n) ∘ S^[n] ∘ (extChartAt I (a 0)).symm)
      ((extChartAt I (a 0)) x) := by
  let f (t : ℕ) := localMap I S (a t) (a (t+1))
  let u (t : ℕ) := (extChartAt I (a t)) (S^[t] x)
  have hf (t : ℕ) (ht : t < n) : ContDiffAt ℝ ∞ (f t) (u t) := by
    apply contDiffAt_localMap I S (a t) (a (t+1)) (S^[t] x)
    · exact ⟨by simpa only [extChartAt_source] using hx t ht.le,
        by simpa only [extChartAt_source,Set.mem_preimage,Function.iterate_succ_apply'] using hx (t+1) (by omega)⟩
    · exact hi t ht.le
  have ho (t : ℕ) (ht : t < n) : f t (u t)=u (t+1) := by
    simp only [f,u,localMap,Function.comp_apply,(extChartAt I (a t)).left_inv (hx t ht.le),
      Function.iterate_succ_apply']
  have hs := ShortDerivative.contDiffAt_iterate f u n ho hf
  have he := iterate_localMap_germ I S a x n hx (by simpa using hi 0 (Nat.zero_le n))
  exact hs.congr_of_eventuallyEq he.symm

/-- The old endpoint differential is exactly the transition of its real
one-step gauge. This equality permits relative exterior control to feed the
leading-minor estimate at zero rank as well as positive rank. -/
theorem actual_endpoint_differential (S : Diffeomorph I I M M ∞) (a : ℕ → M)
    (x : M) (n : ℕ) (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hx : ∀ t ≤ n,S^[t] x∈(extChartAt I (a t)).source)
    (hi : ∀ t ≤ n,(extChartAt I (a t)) (S^[t] x)∈interior (range I))
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (hstep : ∀ t < n,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
      (coord I S (a t) (a (t+1)) (S^[t] x))*U t=U (t+1)*rate lam 1) :
    HasFDerivAt (extChartAt I (a n) ∘ S^[n] ∘ (extChartAt I (a 0)).symm)
      (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam 0 n))
        ((extChartAt I (a 0)) x) := by
  let f (t : ℕ) := localMap I S (a t) (a (t+1))
  let u (t : ℕ) := (extChartAt I (a t)) (S^[t] x)
  have hf (t : ℕ) (ht : t < n) : HasFDerivAt (f t)
      (coord I S (a t) (a (t+1)) (S^[t] x)) (u t) := by
    apply hasFDerivAt_localMap I S (a t) (a (t+1)) (S^[t] x)
    · exact ⟨by simpa only [extChartAt_source] using hx t ht.le,
        by simpa only [extChartAt_source,Set.mem_preimage,Function.iterate_succ_apply'] using hx (t+1) (by omega)⟩
    · exact hi t ht.le
  have ho (t : ℕ) (ht : t < n) : f t (u t)=u (t+1) := by
    simp only [f,u,localMap,Function.comp_apply,(extChartAt I (a t)).left_inv (hx t ht.le),
      Function.iterate_succ_apply']
  have hs := EuclideanSplitting.derivative_transition f u U V lam n hUV hVU ho
    (fun t ht => (hf t ht).differentiableAt)
    (fun t ht => by rw [(hf t ht).fderiv]; exact hstep t ht)
  have he := iterate_localMap_germ I S a x n hx (by simpa using hi 0 (Nat.zero_le n))
  exact hs.congr_of_eventuallyEq he.symm
end SmoothObstruction.ManifoldCoordinates

end

end OAI
