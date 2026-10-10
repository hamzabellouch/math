import OAI.Dynamics.SmoothObstruction.ProductCoordinates
import OAI.Dynamics.SmoothObstruction.GridCells
import OAI.Dynamics.SmoothObstruction.ShortScales

namespace OAI

section

namespace SmoothObstruction.ManifoldCoordinates
open Set MeasureTheory FiniteBins
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    {ι : Type*} [Fintype ι]
open ChartDensity

/-- The actual full finite product partition is constructed from one original
gauge reference per active starting bin. Wall strips are charged to the ORIGINAL
measure. No endpoint or orbit chart code is included in the cell alphabet. The
recovery assertion is precisely the ideal exchange needed by both joins. -/
theorem finite_product_partition_uniform (μ : Measure M) [IsProbabilityMeasure μ]
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    (c : M → ι) (hc : ∀ x,x∈K (c x)) :
    ∃ D : ℝ,1≤D ∧ ∀ (C : Type*) [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C] (P : M → C),Measurable P → ∀ (chart : C → ι),
      (∀ x,chart (P x)=c x) → ∀ (G : Set M) (n : ℕ) (B R : ℝ),0≤B →
      ∀ (A : ∀ x:G,BilateralGauge I S a c n B R x) (T : G → Finset (Fin d))
        (δ : ℝ),0<δ → ∀ N : ℕ,0<N →
      let H₀ := Real.sqrt 2*Real.exp (2*B)
      let m := ⌈H₀*D/(δ*N)+1⌉₊
      ∃ (L : M → C × (Fin d → Fin (2*m+1))) (W : Set M),
        Measurable L ∧ MeasurableSet W ∧ μ.real W≤(d:ℝ)/N ∧
        (∀ x,(L x).1=P x) ∧
        (∀ x y,L x=L y →
          ‖coordinates I (a (c x)) x-coordinates I (a (c x)) y‖≤
            Real.sqrt 2*((d:ℝ)+1)*(δ*N)) ∧
        (∀ (x y z : M) (hx : x∈G),L x=L y → x∉W → y∉W → P z=P x →
          let ref : G := (reference P G (key P G ⟨x,hx⟩)).val
          H₀*‖coordinates I (a (c x)) z-(coordinates I (a (c x)) x+
            (((A ref).forward I S a c).splitting (T ref)ᶜ).slow 0
              (coordinates I (a (c x)) y-coordinates I (a (c x)) x))‖≤δ/4 →
          L z=L x) ∧
        Fintype.card (C × (Fin d → Fin (2*m+1)))=Fintype.card C*(2*m+1)^d := by
  obtain ⟨D,hD,hbound⟩ := selected_coordinate_bound I a K hK hKU c hc
  refine ⟨D,hD,?_⟩
  intro C _ _ _ P hP chart hchart G n B R hB A T δ hδ N hN H₀ m
  let ref (Q : Active P G) : G := (reference P G Q).val
  obtain ⟨E,hE,hEi,hmix⟩ := product_coordinates P G hB
    (fun Q => (A (ref Q)).forward I S a c) (fun Q => (T (ref Q))ᶜ)
  let φ (Q : C) (x : M) := coordinates I (a (chart Q)) x
  have hb (x : M) : ‖φ (P x) x‖≤D := by simpa only [φ,hchart] using hbound x
  obtain ⟨L,W,hL,hW,hWm,hLP,hdiam,hstable,hcard⟩ := ProductCells.exists_cells μ P hP φ
    (fun Q => measurable_coordinates I (a (chart Q))) E (show 0≤D by linarith)
    (show 0≤H₀ by dsimp [H₀]; positivity) (Real.sqrt_nonneg _) hδ hb hEi hE hN
  refine ⟨L,W,hL,hW,hWm,hLP,?_,?_,hcard⟩
  · intro x y hxy
    simpa only [φ,hchart] using hdiam x y hxy
  · intro x y z hx hxy hxW hyW hz ref₀ herror
    apply hstable x y z hxy hxW hyW hz
    let Q : Active P G := key P G ⟨x,hx⟩
    let ideal := φ (P x) x+(((A (ref Q)).forward I S a c).splitting (T (ref Q))ᶜ).slow 0
      (φ (P x) y-φ (P x) x)
    have herr : H₀*‖φ (P x) z-ideal‖≤δ/4 := by
      simpa only [ideal,φ,hchart,ref,Q] using herror
    have he (i : Fin d) : |((E (P x)).symm (φ (P x) z)) i-((E (P x)).symm ideal) i|≤δ/4 := by
      calc
        _ = ‖(((E (P x)).symm (φ (P x) z-ideal)) i)‖ := by rw [map_sub]; rfl
        _ ≤ ‖(E (P x)).symm (φ (P x) z-ideal)‖ := PiLp.norm_apply_le _ _
        _ ≤ ‖(E (P x)).symm.toContinuousLinearMap‖*‖φ (P x) z-ideal‖ :=
          (E (P x)).symm.toContinuousLinearMap.le_opNorm _
        _ ≤ H₀*‖φ (P x) z-ideal‖ := mul_le_mul_of_nonneg_right (hEi _) (norm_nonneg _)
        _ ≤ δ/4 := herr
    intro i
    have hh := hmix Q (φ (P x) x) (φ (P x) y) i
    change ((E (P x)).symm ideal) i=((E (P x)).symm (φ (P x) x)) i ∨
      ((E (P x)).symm ideal) i=((E (P x)).symm (φ (P x) y)) i at hh
    rcases hh with hh|hh
    · exact Or.inl (by simpa only [hh] using he i)
    · exact Or.inr (by simpa only [hh] using he i)
end SmoothObstruction.ManifoldCoordinates

end

section

open Filter Topology
open scoped Real

namespace SmoothObstruction.SwitchScales
open Filter Topology
open scoped Real
noncomputable def shortTime (b n : ℝ) : ℕ := ⌈b^(1/4:ℝ)*n⌉₊
noncomputable def root (b : ℝ) : ℝ := b^(1/8:ℝ)
noncomputable def gap (b : ℝ) : ℝ := b^(1/2:ℝ)
noncomputable def shortSignal (b n : ℝ) : ℝ := b^(3/4:ℝ)*n

lemma ceil_bounds {b n : ℝ} (hn : 1≤n) (hfloor : n^(-1/10:ℝ)≤b) :
    b^(1/4:ℝ)*n≤(shortTime b n : ℝ) ∧ (shortTime b n : ℝ)≤2*b^(1/4:ℝ)*n := by
  have hl := ScaleHierarchy.lower_bound (p:=1/4) hn (by norm_num) hfloor
  have hp : 1≤b^(1/4:ℝ)*n := by
    apply le_trans _ hl
    exact Real.one_le_rpow hn (by norm_num)
  refine ⟨Nat.le_ceil _,?_⟩
  have hh := Nat.ceil_lt_add_one (show 0≤b^(1/4:ℝ)*n by linarith)
  change (shortTime b n : ℝ)<b^(1/4:ℝ)*n+1 at hh
  linarith

lemma gap_short_lower {b n : ℝ} (hb : 0<b) :
    shortSignal b n≤gap b*(shortTime b n : ℝ) := by
  have hh := mul_le_mul_of_nonneg_left (Nat.le_ceil (b^(1/4:ℝ)*n))
    (Real.rpow_nonneg hb.le (1/2:ℝ))
  have he : b^(1/2:ℝ)*(b^(1/4:ℝ)*n)=shortSignal b n := by
    rw [←mul_assoc,←Real.rpow_add hb]; norm_num [shortSignal]
  rwa [he] at hh

lemma short_eventually {ι : Type*} {l : Filter ι} {b n : ι → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k) :
    ∀ᶠ k in l,(shortTime (b k) (n k) : ℝ)≤n k ∧ 0<b k ∧ b k≤1 ∧ 1≤n k ∧
      (shortTime (b k) (n k) : ℝ)≤2*b k^(1/4:ℝ)*n k := by
  have hr : Tendsto (fun k => b k^(1/4:ℝ)) l (𝓝 0) := by
    simpa only [Real.zero_rpow (by norm_num : (1/4:ℝ)≠0),Function.comp_def] using
      ((Real.continuous_rpow_const (show (0:ℝ)≤1/4 by norm_num)).tendsto 0).comp hb
  filter_upwards [hbpos,hn.eventually (eventually_ge_atTop 1),
    hb.eventually_le_const (by norm_num : (0:ℝ)<1),
    hr.eventually_le_const (by norm_num : (0:ℝ)<1/2),hfloor] with k hp hn1 hb1 hr1 hf
  have hL := (ceil_bounds hn1 hf).2
  refine ⟨hL.trans ?_,hp,hb1,hn1,hL⟩
  nlinarith [mul_le_mul_of_nonneg_right hr1 (show 0≤n k by linarith)]

/-- The genuine short-product noise with its ceiling time is swallowed by
one original spatial exponent, even after a full short-gap exponential cost. -/
theorem short_noise_decay {ι : Type*} {l : Filter ι} {b n : ι → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    {J C : ℝ} (hJ : 0≤J) (hC : 0≤C) :
    Tendsto (fun k => n k*Real.exp (J*(shortTime (b k) (n k):ℝ)+C*b k*n k+
      shortSignal (b k) (n k)-root (b k)*n k)) l (𝓝 0) := by
  have hz := ScaleHierarchy.polynomial_decay (p:=1/8) (q:=1/4) (c:=1)
    (C:=2*J+C+1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hbpos hb hn hfloor 1
  simp only [pow_one,one_mul] at hz
  apply squeeze_zero' _ _ hz
  · filter_upwards [hn.eventually (eventually_ge_atTop 0)] with k hk
    exact mul_nonneg hk (Real.exp_pos _).le
  · filter_upwards [short_eventually hbpos hb hn hfloor] with k hk
    have hbq : b k≤b k^(1/4:ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hk.2.1 hk.2.2.1
        (show (1/4:ℝ)≤1 by norm_num)
    have hb3 : b k^(3/4:ℝ)≤b k^(1/4:ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hk.2.1 hk.2.2.1 (by norm_num)
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by linarith [hk.2.2.2.1])
    have h₁ := mul_le_mul_of_nonneg_left hk.2.2.2.2 hJ
    have h₂ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbq hC)
      (show 0≤n k by linarith [hk.2.2.2.1])
    have h₃ := mul_le_mul_of_nonneg_right hb3 (show 0≤n k by linarith [hk.2.2.2.1])
    dsimp [shortSignal,root]
    nlinarith

/-- All common-bin projector errors, including the true product difference
`L C C^(2L) h0`, are exponentially small at the authentic gap×time scale. -/
theorem projector_budget {ι : Type*} {l : Filter ι} {b n : ι → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    {C D A : ℝ} (hC : 1≤C) (hD : 0≤D) (hA : 0≤A) :
    let L (k : ι) := shortTime (b k) (n k)
    let K (k : ι) := D*b k*n k
    let noise (k : ι) := (L k:ℝ)*C*C^(2*L k)*Real.exp (-root (b k)*n k)
    let err (k : ι) := Real.exp (-2*gap (b k)*(L k:ℝ)+4*K k)+
      noise k*Real.exp (A*gap (b k)*(L k:ℝ)+2*K k)
    ∀ᶠ k in l,3*err k≤Real.exp (-shortSignal (b k) (n k)) := by
  intro L K noise err
  have hlog : 0≤Real.log C := Real.log_nonneg hC
  have hz₁ := ScaleHierarchy.polynomial_decay (p:=3/4) (q:=1) (c:=1) (C:=4*D)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbpos hb hn hfloor 0
  simp only [pow_zero,one_mul,Real.rpow_one] at hz₁
  have hz₂ := (short_noise_decay hbpos hb hn hfloor
    (J:=2*Real.log C+A) (C:=2*D) (by positivity) (by positivity)).const_mul C
  simp only [mul_zero] at hz₂
  have hz : Tendsto (fun k => 3*(Real.exp (4*D*b k*n k-shortSignal (b k) (n k))+
      C*(n k*Real.exp ((2*Real.log C+A)*(L k:ℝ)+2*D*b k*n k+
        shortSignal (b k) (n k)-root (b k)*n k)))) l (𝓝 0) := by
    simpa only [add_zero,mul_zero,shortSignal,L] using (hz₁.add hz₂).const_mul 3
  filter_upwards [short_eventually hbpos hb hn hfloor,
    hz.eventually_le_const (by norm_num : (0:ℝ)<1)] with k hk hzbound
  have hg : gap (b k)≤1 := Real.rpow_le_one hk.2.1.le hk.2.2.1 (by norm_num)
  have hnp : 0≤n k := by linarith [hk.2.2.2.1]
  have hL : 0≤(L k:ℝ) := Nat.cast_nonneg _
  have heC : C^(2*L k)=Real.exp (2*Real.log C*(L k:ℝ)) := by
    rw [show 2*Real.log C*(L k:ℝ)=((2*L k:ℕ):ℝ)*Real.log C by push_cast; ring,
      Real.exp_nat_mul,Real.exp_log (by linarith : 0<C)]
  have hfirst : Real.exp (-2*gap (b k)*(L k:ℝ)+4*K k)*
      Real.exp (shortSignal (b k) (n k))≤
      Real.exp (4*D*b k*n k-shortSignal (b k) (n k)) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := gap_short_lower (n:=n k) hk.2.1
    dsimp only [K,L]
    linarith
  have hsecond : noise k*Real.exp (A*gap (b k)*(L k:ℝ)+2*K k)*
      Real.exp (shortSignal (b k) (n k))≤
      C*(n k*Real.exp ((2*Real.log C+A)*(L k:ℝ)+2*D*b k*n k+
        shortSignal (b k) (n k)-root (b k)*n k)) := by
    dsimp only [noise]
    rw [heC]
    have he : (L k:ℝ)*C*Real.exp (2*Real.log C*(L k:ℝ))*Real.exp (-root (b k)*n k)*
        Real.exp (A*gap (b k)*(L k:ℝ)+2*K k)*Real.exp (shortSignal (b k) (n k))=
        C*((L k:ℝ)*Real.exp (2*Real.log C*(L k:ℝ)-root (b k)*n k+
          (A*gap (b k)*(L k:ℝ)+2*K k)+shortSignal (b k) (n k))) := by
      simp only [sub_eq_add_neg,neg_mul,Real.exp_add,Real.exp_neg]
      ring
    rw [he]
    apply mul_le_mul_of_nonneg_left _ (by linarith : 0≤C)
    apply mul_le_mul hk.1 (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hnp
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg hA) hL
    dsimp only [K]
    nlinarith
  have hbound : 3*err k*Real.exp (shortSignal (b k) (n k))≤1 := by
    dsimp only [err]
    have hh := mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (by norm_num : (0:ℝ)≤3)
    calc
      _ = 3*(Real.exp (-2*gap (b k)*(L k:ℝ)+4*K k)*Real.exp (shortSignal (b k) (n k))+
        noise k*Real.exp (A*gap (b k)*(L k:ℝ)+2*K k)*Real.exp (shortSignal (b k) (n k))) := by ring
      _ ≤ _ := hh
      _ ≤ 1 := hzbound
  have he : Real.exp (-shortSignal (b k) (n k))*Real.exp (shortSignal (b k) (n k))=1 := by
    rw [←Real.exp_add,neg_add_cancel,Real.exp_zero]
  exact (mul_le_mul_iff_left₀ (Real.exp_pos _)).mp (hbound.trans_eq he.symm)
end SmoothObstruction.SwitchScales

end

section

namespace SmoothObstruction.SwitchScales
open Filter Topology
/-- A simultaneous usable envelope for all starting/endpoint bin estimates.
The short time is still the source ceiling, not an adjustable subsequence. -/
theorem reference_budget {ι : Type*} {l : Filter ι} {b n : ι → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    {C D A r : ℝ} (hC : 1≤C) (hD : 0≤D) (hA : 0≤A) (hr : 0<r) :
    let L (k : ι) := shortTime (b k) (n k)
    let K (k : ι) := D*b k*n k
    let h (k : ι) := Real.exp (-root (b k)*n k)
    let noise (k : ι) := (L k:ℝ)*C*C^(2*L k)*h k
    let err (k : ι) := Real.exp (-2*gap (b k)*(L k:ℝ)+4*K k)+
      noise k*Real.exp (A*gap (b k)*(L k:ℝ)+2*K k)
    ∀ᶠ k in l,(L k:ℝ)≤n k ∧ 1≤(L k:ℝ) ∧
      C^(L k)*h k≤r ∧ noise k<Real.exp (-2*K k)/2 ∧
      Real.exp (-2*gap (b k)*(L k:ℝ)+4*K k)≤1/2 ∧ err k≤1/2 ∧
      3*err k≤Real.exp (-shortSignal (b k) (n k)) ∧
      Real.exp (-shortSignal (b k) (n k))≤1/2 := by
  intro L K h noise err
  have he := ScaleHierarchy.polynomial_decay (p:=3/4) (q:=1) (c:=1) (C:=0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbpos hb hn hfloor 0
  simp only [pow_zero,one_mul,zero_mul,zero_sub] at he
  have he' : Tendsto (fun k => Real.exp (-shortSignal (b k) (n k))) l (𝓝 0) := by
    simpa only [shortSignal,neg_mul] using he
  filter_upwards [projector_budget hbpos hb hn hfloor hC hD hA,
    short_eventually hbpos hb hn hfloor,hfloor,
    he'.eventually_le_const (lt_min (by norm_num : (0:ℝ)<1/4) hr)] with k hbudget ht hf he
  have hL : 1≤(L k:ℝ) := by
    have hh := ScaleHierarchy.lower_bound (p:=1/4) ht.2.2.2.1 (by norm_num) hf
    have hrp := Real.one_le_rpow ht.2.2.2.1 (by norm_num : (0:ℝ)≤1-(1/4:ℝ)/10)
    exact (hrp.trans hh).trans (Nat.le_ceil _)
  have hK : 0≤K k := mul_nonneg (mul_nonneg hD ht.2.1.le) (by linarith [ht.2.2.2.1])
  have hg : 0≤gap (b k) := Real.rpow_nonneg ht.2.1.le _
  have hnz : 0≤noise k := by dsimp only [noise,h]; positivity
  have hLeft : Real.exp (-2*gap (b k)*(L k:ℝ)+4*K k)≤err k := by
    exact le_add_of_nonneg_right (mul_nonneg hnz (Real.exp_pos _).le)
  have hnoise : noise k≤err k := by
    have hex : 1≤Real.exp (A*gap (b k)*(L k:ℝ)+2*K k) := Real.one_le_exp_iff.mpr (by positivity)
    have hh := mul_le_mul_of_nonneg_left hex hnz
    dsimp only [err]; nlinarith [Real.exp_pos (-2*gap (b k)*(L k:ℝ)+4*K k)]
  have hne : noise k*Real.exp (2*K k)≤err k := by
    have hex : Real.exp (2*K k)≤Real.exp (A*gap (b k)*(L k:ℝ)+2*K k) := Real.exp_le_exp.mpr (le_add_of_nonneg_left (mul_nonneg (mul_nonneg hA hg) (Nat.cast_nonneg _)))
    have hh := mul_le_mul_of_nonneg_left hex hnz
    dsimp only [err]; linarith [Real.exp_pos (-2*gap (b k)*(L k:ℝ)+4*K k)]
  have herr : err k≤1/4 := by
    have h := he.trans (min_le_left _ _)
    have herrpos : 0≤err k := (Real.exp_pos _).le.trans hLeft
    linarith
  refine ⟨ht.1,hL,?_,?_,hLeft.trans (by linarith),by linarith,hbudget,he.trans (by linarith [min_le_left (1/4:ℝ) r])⟩
  · have hp : C^(L k)≤C^(2*L k) := pow_le_pow_right₀ hC (by omega)
    have hc : 1≤(L k:ℝ)*C := one_le_mul_of_one_le_of_one_le hL hC
    have hn : C^(L k)*h k≤noise k := by
      dsimp only [noise]
      calc
        _ ≤ C^(2*L k)*h k := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
        _ ≤ ((L k:ℝ)*C)*C^(2*L k)*h k := by
          have hh := mul_le_mul_of_nonneg_right hc (mul_nonneg (pow_nonneg (by linarith : 0≤C) (2*L k)) (show 0≤h k from (Real.exp_pos _).le))
          simpa only [one_mul,mul_assoc] using hh
    have hre : Real.exp (-shortSignal (b k) (n k))≤r := he.trans (min_le_right _ _)
    have herrpos : 0≤err k := (Real.exp_pos _).le.trans hLeft
    exact hn.trans (hnoise.trans (by linarith))
  · have hmul := mul_lt_mul_of_pos_right (show noise k*Real.exp (2*K k)<1/2 by linarith)
      (Real.exp_pos (-2*K k))
    have heq : Real.exp (2*K k)*Real.exp (-2*K k)=1 := by rw [←Real.exp_add]; simp
    calc
      _ = (noise k*Real.exp (2*K k))*Real.exp (-2*K k) := by rw [mul_assoc,heq,mul_one]
      _ < _ := hmul
      _ = _ := by ring
end SmoothObstruction.SwitchScales

namespace SmoothObstruction.SwitchScales
open Filter Topology
/-- The finite-time noise is monotone in the literal chart constant. -/
def refNoise (C : ℝ) (N : ℕ) (h : ℝ) : ℝ := (N:ℝ)*C*C^(2*N)*h

noncomputable def refError (K A g : ℝ) (N : ℕ) (noise : ℝ) : ℝ :=
  Real.exp (-2*g*N+4*K)+noise*Real.exp (A*g*N+2*K)

theorem refNoise_nonneg {C h : ℝ} (hC : 0≤C) (hh : 0≤h) (N : ℕ) :
    0≤refNoise C N h := by unfold refNoise; positivity

theorem refNoise_mono {C D h : ℝ} {N : ℕ} (hC : 0≤C) (hCD : C≤D) (hh : 0≤h) :
    refNoise C N h≤refNoise D N h := by
  have hD : 0≤D := hC.trans hCD
  apply mul_le_mul_of_nonneg_right _ hh
  apply mul_le_mul (mul_le_mul_of_nonneg_left hCD (Nat.cast_nonneg N))
    (pow_le_pow_left₀ hC hCD (2*N)) (pow_nonneg hC _) (by positivity)

theorem refNoise_add_le {C₁ C₂ C h : ℝ} {N : ℕ}
    (h₁ : 0≤C₁) (h₂ : 0≤C₂) (hC : C₁+C₂≤C) (hh : 0≤h) :
    refNoise C₁ N h+refNoise C₂ N h≤refNoise C N h := by
  have hc₁ : C₁≤C := by linarith
  have hc₂ : C₂≤C := by linarith
  have hpow₁ := pow_le_pow_left₀ h₁ hc₁ (2*N)
  have hpow₂ := pow_le_pow_left₀ h₂ hc₂ (2*N)
  calc
    _ ≤ (N:ℝ)*C₁*C^(2*N)*h+(N:ℝ)*C₂*C^(2*N)*h := by
      exact add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow₁ (by positivity)) hh)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow₂ (by positivity)) hh)
    _ = (N:ℝ)*(C₁+C₂)*C^(2*N)*h := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hh
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg N)) (pow_nonneg (by linarith) _)

theorem refError_mono {K₀ K A g noise₀ noise : ℝ} {N : ℕ}
    (hK : K₀≤K) (hn : 0≤noise₀) (hnoise : noise₀≤noise) :
    refError K₀ A g N noise₀≤refError K A g N noise := by
  apply add_le_add (Real.exp_le_exp.mpr (by linarith))
  exact mul_le_mul hnoise (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
    (hn.trans hnoise)

theorem endpoint_refError_le {K₀ K A g u noise₀ noise : ℝ} {N : ℕ}
    (hK : K₀≤K) (hu : u≤A*g) (hn : 0≤noise₀) (hnoise : noise₀≤noise) :
    Real.exp (u*N+2*K₀)*(Real.exp ((-2*g-u)*N+2*K₀)+noise₀)≤refError K A g N noise := by
  rw [mul_add,←Real.exp_add]
  have he : u*(N:ℝ)+2*K₀+((-2*g-u)*N+2*K₀)=-2*g*N+4*K₀ := by ring
  rw [he]
  apply add_le_add (Real.exp_le_exp.mpr (by linarith))
  rw [mul_comm]
  apply mul_le_mul hnoise _ (Real.exp_pos _).le (hn.trans hnoise)
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_right hu (Nat.cast_nonneg N)
  linarith

/-- All model-dependent reference constants are absorbed without changing b,n
or the source short-time, mesh and clean projector-error scales. -/
theorem reference_constants_eventually {κ : Type*} {l : Filter κ} {b n : κ → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    (d : ℕ) {Dg C₁ C₂ C₃ C₄ D D₃ D₄ r₁ r₂ r₃ r₄ : ℝ}
    (hDg : 0≤Dg) (hC₁ : 1≤C₁) (hC₂ : 1≤C₂) (hC₃ : 1≤C₃) (hC₄ : 1≤C₄)
    (hD : 1≤D) (hD₃ : 1≤D₃) (hD₄ : 1≤D₄)
    (hr₁ : 0<r₁) (hr₂ : 0<r₂) (hr₃ : 0<r₃) (hr₄ : 0<r₄) :
    let L (k : κ) := shortTime (b k) (n k)
    let B (k : κ) := Dg*(b k*n k)
    let h (k : κ) := Real.exp (-root (b k)*n k)
    let g (k : κ) := gap (b k)
    let ε (k : κ) := Real.exp (-shortSignal (b k) (n k))
    let err (k : κ) := refError (B k+Real.log D) (1+8*d) (g k) (L k)
      (refNoise C₁ (L k) (h k)+refNoise C₂ (L k) (h k))
    ∀ᶠ k in l,(L k:ℝ)≤n k ∧ 1≤(L k:ℝ) ∧ 0<g k ∧
      C₁^(L k)*h k≤r₁ ∧ C₂^(L k)*h k≤r₂ ∧ C₃^(L k)*h k≤r₃ ∧ C₄^(L k)*h k≤r₄ ∧
      refNoise C₁ (L k) (h k)+refNoise C₂ (L k) (h k)<Real.exp (-2*(B k+Real.log D))/2 ∧
      Real.exp (-2*g k*(L k:ℝ)+4*(B k+Real.log D))≤1/2 ∧
      err k≤1/2 ∧ 3*err k≤ε k ∧ ε k≤1/2 ∧
      ∀ j : Fin (d+1),let γ := (1+8*(j.val:ℝ))*g k
        (Real.exp ((γ-g k)*(L k:ℝ)+2*(B k+Real.log D₃))*
          (Real.exp ((-γ-g k)*(L k:ℝ)+2*(B k+Real.log D₃))+refNoise C₃ (L k) (h k))≤ε k/3) ∧
        (Real.exp ((-γ-g k)*(L k:ℝ)+2*(B k+Real.log D₄))*
          (Real.exp ((γ-g k)*(L k:ℝ)+2*(B k+Real.log D₄))+refNoise C₄ (L k) (h k))≤ε k/3) := by
  intro L B h g ε err
  let C := C₁+C₂+C₃+C₄+1
  let Dbar := Dg+Real.log D+Real.log D₃+Real.log D₄
  have hlD := Real.log_nonneg hD
  have hlD₃ := Real.log_nonneg hD₃
  have hlD₄ := Real.log_nonneg hD₄
  have hDb : 0≤Dbar := by dsimp [Dbar]; positivity
  have hC : 1≤C := by dsimp [C]; linarith
  have hc₁ : C₁≤C := by dsimp [C]; linarith
  have hc₂ : C₂≤C := by dsimp [C]; linarith
  have hc₃ : C₃≤C := by dsimp [C]; linarith
  have hc₄ : C₄≤C := by dsimp [C]; linarith
  have hc12 : C₁+C₂≤C := by dsimp [C]; linarith
  have hr : 0 < min (min r₁ r₂) (min r₃ r₄) := lt_min (lt_min hr₁ hr₂) (lt_min hr₃ hr₄)
  have hbudget := reference_budget hbpos hb hn hfloor hC hDb (by positivity : 0≤(1+8*(d:ℝ))) hr
  filter_upwards [hbudget,hbpos,hfloor,hn.eventually (eventually_ge_atTop (1:ℝ))] with k ht hbpos hf hn1
  let K := Dbar*b k*n k
  let noise := refNoise C (L k) (h k)
  let e := refError K (1+8*d) (g k) (L k) noise
  have hbn : 1≤b k*n k := by
    have hs := ScaleHierarchy.lower_bound (p:=1) hn1 (by norm_num) hf
    have hpow := Real.one_le_rpow hn1 (by norm_num : (0:ℝ)≤1-(1:ℝ)/10)
    simpa only [Real.rpow_one] using hpow.trans hs
  have hK (D' : ℝ) (hD' : 0≤Real.log D') (hd : Dg+Real.log D'≤Dbar) : B k+Real.log D'≤K := by
    have hm := mul_le_mul_of_nonneg_right hd (by linarith : 0≤b k*n k)
    have hm' := mul_le_mul_of_nonneg_left hbn hD'
    dsimp only [B,K]
    nlinarith only [hm,hm']
  have hKD := hK D hlD (by dsimp [Dbar]; linarith)
  have hKD₃ := hK D₃ hlD₃ (by dsimp [Dbar]; linarith)
  have hKD₄ := hK D₄ hlD₄ (by dsimp [Dbar]; linarith)
  have hhp : 0≤h k := (Real.exp_pos _).le
  have hn12 : refNoise C₁ (L k) (h k)+refNoise C₂ (L k) (h k)≤noise :=
    refNoise_add_le (by linarith) (by linarith) hc12 hhp
  have hn3 : refNoise C₃ (L k) (h k)≤noise := refNoise_mono (by linarith) hc₃ hhp
  have hn4 : refNoise C₄ (L k) (h k)≤noise := refNoise_mono (by linarith) hc₄ hhp
  have he : err k≤e := refError_mono hKD (by apply add_nonneg <;> apply refNoise_nonneg <;> linarith) hn12
  have hτ (C' r' : ℝ) (hC' : 0≤C') (hc' : C'≤C) (hr' : min (min r₁ r₂) (min r₃ r₄)≤r') :
      C'^(L k)*h k≤r' :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC' hc' _) hhp).trans (ht.2.2.1.trans hr')
  have hg : 0<g k := Real.rpow_pos_of_pos hbpos _
  refine ⟨ht.1,ht.2.1,hg,hτ C₁ r₁ (by linarith) hc₁ ((min_le_left _ _).trans (min_le_left _ _)),
    hτ C₂ r₂ (by linarith) hc₂ ((min_le_left _ _).trans (min_le_right _ _)),
    hτ C₃ r₃ (by linarith) hc₃ ((min_le_right _ _).trans (min_le_left _ _)),
    hτ C₄ r₄ (by linarith) hc₄ ((min_le_right _ _).trans (min_le_right _ _)),?_,?_,?_,?_,ht.2.2.2.2.2.2.2,?_⟩
  · exact (hn12.trans_lt ht.2.2.2.1).trans_le (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by norm_num))
  · exact (Real.exp_le_exp.mpr (by linarith : -2*g k*(L k:ℝ)+4*(B k+Real.log D)≤-2*g k*(L k:ℝ)+4*K)).trans ht.2.2.2.2.1
  · exact he.trans ht.2.2.2.2.2.1
  · exact (mul_le_mul_of_nonneg_left he (by norm_num)).trans ht.2.2.2.2.2.2.1
  · intro j γ
    have hj : (j.val:ℝ)≤d := by exact_mod_cast (show j.val≤d by omega)
    have hγ₀ : 0≤γ := by dsimp only [γ]; positivity
    have hγ : γ≤(1+8*(d:ℝ))*g k := by
      apply mul_le_mul_of_nonneg_right _ hg.le
      linarith
    have hf := endpoint_refError_le (N:=L k) hKD₃
      (show γ-g k≤(1+8*(d:ℝ))*g k by linarith) (refNoise_nonneg (by linarith : 0≤C₃) hhp _) hn3
    have hb := endpoint_refError_le (N:=L k) hKD₄
      (show -γ-g k≤(1+8*(d:ℝ))*g k by linarith) (refNoise_nonneg (by linarith : 0≤C₄) hhp _) hn4
    have he3 : e≤ε k/3 := by have hh := ht.2.2.2.2.2.2.1; change 3*e≤ε k at hh; linarith
    constructor
    · convert hf.trans he3 using 1; congr 3; ring
    · convert hb.trans he3 using 1; congr 3; ring
end SmoothObstruction.SwitchScales

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology Metric MeasureTheory FiniteBins ShortBin SwitchScales
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- Authentic finite-bin references on every sufficiently large original scale.
The constants depend on the model and atlas, not the scale, alphabets, gauges,
or good set. The clean error is exp(-b^(3/4)n). -/
theorem eventual_finite_references (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    {κ : Type*} {l : Filter κ} {b : κ → ℝ} {n : κ → ℕ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto (fun k => (n k:ℝ)) l atTop)
    (hfloor : ∀ᶠ k in l,(n k:ℝ)^(-1/10:ℝ)≤b k)
    (Dg R : ℝ) (hDg : 0≤Dg) :
    ∀ᶠ k in l,∀ (C : Type*) (c : M → ι) (P : M → C) (G : Set M)
      (A : ∀ x:G,BilateralGauge I S a c (n k) (Dg*(b k*n k)) R x),
      (∀ y,y∈K (c y)) → (∀ x y,P x=P y → c x=c y) →
      (∀ x∈G,I.IsInteriorPoint x) →
      (∀ x y,P x=P y → ‖(extChartAt I (a (c y))) x-(extChartAt I (a (c y))) y‖≤
        Real.exp (-root (b k)*n k)) →
      ∃ (γ : C → ℝ) (T : G → Finset (Fin d)) (ref : G → G)
        (Wf Wb : C×C → Submodule ℝ E₀),
        (ref = fun x => (reference P G (key P G x)).val) ∧
        (∀ q,|γ q|+|gap (b k)|≤(2+8*(d:ℝ))*gap (b k)) ∧
        (∀ x:G,P (ref x)=P x) ∧
        (∀ x y:G,P x=P y → (T x).card=(T y).card) ∧
        (∀ x y:G,P x=P y → ref x=ref y) ∧
        (∀ x:G,∀ i∈(T x)ᶜ,(A x).lam i≤γ (P x)-gap (b k)) ∧
        (∀ x:G,∀ i∈T x,γ (P x)+gap (b k)≤(A x).lam i) ∧
        (∀ x:G,
          ‖((A (ref x)).forwardSpace I S a c 0 (T (ref x))ᶜ).starProjection-
            ((A x).forwardSpace I S a c 0 (T x)ᶜ).starProjection‖≤Real.exp (-shortSignal (b k) (n k)) ∧
          ‖((A (ref x)).forwardSpace I S a c 0 (T (ref x))).starProjection-
            ((A x).forwardSpace I S a c 0 (T x)).starProjection‖≤Real.exp (-shortSignal (b k) (n k))) ∧
        (∀ x:G,
          Module.finrank ℝ (Wf (P x,P (S^[n k] x)))=(T x).card ∧
          Module.finrank ℝ (Wb (P x,P (S.symm^[n k] x)))=d-(T x).card ∧
          ‖((A x).forwardSpace I S a c (n k) (T x)).starProjection-
            (Wf (P x,P (S^[n k] x))).starProjection‖≤1/2 ∧
          ‖((A x).backwardSpace I S a c (n k) (T x)ᶜ).starProjection-
            (Wb (P x,P (S.symm^[n k] x))).starProjection‖≤1/2) := by
  classical
  obtain ⟨r₁,C₁,r₂,C₂,D,r₃,C₃,D₃,r₄,C₄,D₄,hr₁,hC₁,hr₂,hC₂,hD,hr₃,hC₃,hD₃,hr₄,hC₄,hD₄,hrefs⟩ :=
    finite_references_uniform I hclosed S a K hK hKU
  have hbudget := reference_constants_eventually hbpos hb hn hfloor d hDg hC₁ hC₂ hC₃ hC₄ hD hD₃ hD₄ hr₁ hr₂ hr₃ hr₄
  filter_upwards [hbudget] with k hk
  rcases hk with ⟨hN,hN1,hg,ht₁,ht₂,ht₃,ht₄,hnoise,hdec,herr,herr3,hεhalf,hend⟩
  intro C c P G A hcover hco hint hdiam
  let N := shortTime (b k) (n k)
  let g := gap (b k)
  let h := Real.exp (-root (b k)*n k)
  let B := Dg*(b k*n k)
  let ε := Real.exp (-shortSignal (b k) (n k))
  have hN' : N≤n k := by exact_mod_cast hN
  have hfsmall (j : Fin (d+1)) := (hend j).1
  have hbsmall (j : Fin (d+1)) := (hend j).2
  obtain ⟨j,Wf,Wb,hslow,hfast,hcard,hstart,hend'⟩ := hrefs C c P G (n k) N B R h g A
    hcover hN' hco hint hdiam ht₁ ht₂ ht₃ ht₄ (Real.exp_pos _).le hg hdec
    (by simpa only [refNoise,refError,←add_mul] using And.intro hnoise herr)
    (fun j => by have hh := hfsmall j; change _≤ε/3 at hh; have he : ε≤1/2 := hεhalf; dsimp only [refNoise] at hh; linarith)
    (fun j => by have hh := hbsmall j; change _≤ε/3 at hh; have he : ε≤1/2 := hεhalf; dsimp only [refNoise] at hh; linarith)
  let γ (q : C) := (1+8*((j q).val:ℝ))*g
  let T (x : G) := fastSet (A x).lam (γ (P x))
  let ref (x : G) : G := (reference P G (key P G x)).val
  have hzero (x : G) (U : Finset (Fin d)) :
      ((A x).forward I S a c).space U=(A x).forwardSpace I S a c 0 U := by
    simp only [ShortBin.Gauge.space,BilateralGauge.forward,ShortBin.Gauge.ofFinite,
      Nat.zero_min,BilateralGauge.forwardSpace]
  refine ⟨γ,T,ref,Wf,Wb,rfl,?_,?_,hcard,?_,hslow,hfast,?_,?_⟩
  · intro q
    have hγ : 0≤γ q := by dsimp only [γ]; positivity
    rw [abs_of_nonneg hγ,abs_of_nonneg hg.le]
    have hj : ((j q).val:ℝ)≤d := by exact_mod_cast (show (j q).val≤d by omega)
    have hm := mul_le_mul_of_nonneg_right hj hg.le
    dsimp only [γ]; nlinarith only [hm]
  · intro x; exact (reference P G (key P G x)).property
  · intro x y hxy
    have he : key P G x=key P G y := Subtype.ext hxy
    exact congrArg (fun q : Active P G => (reference P G q).val) he
  · intro x
    have hh := hstart x
    simp only [hzero] at hh
    have he : 3*(Real.exp (-2*g*(N:ℝ)+4*(B+Real.log D))+
        (((N:ℝ)*C₁*C₁^(2*N)+N*C₂*C₂^(2*N))*h)*Real.exp ((1+8*(d:ℝ))*g*N+2*(B+Real.log D)))≤ε := by
      simpa only [refError,refNoise,←add_mul] using herr3
    constructor
    · rw [norm_sub_rev]; exact hh.1.trans he
    · rw [norm_sub_rev]; exact hh.2.trans he
  · intro x
    have hx := hend' x
    refine ⟨hx.1,hx.2.1,?_,?_⟩
    · have hh := hfsmall (j (P x)); dsimp only [refNoise] at hh
      have hb : 3*(Real.exp ((γ (P x)-g)*N+2*(B+Real.log D₃))*
          (Real.exp ((-γ (P x)-g)*N+2*(B+Real.log D₃))+N*C₃*C₃^(2*N)*h))≤ε := by linarith
      exact hx.2.2.1.trans (hb.trans hεhalf)
    · have hh := hbsmall (j (P x)); dsimp only [refNoise] at hh
      have hb : 3*(Real.exp ((-γ (P x)-g)*N+2*(B+Real.log D₄))*
          (Real.exp ((γ (P x)-g)*N+2*(B+Real.log D₄))+N*C₄*C₄^(2*N)*h))≤ε := by linarith
      exact hx.2.2.2.trans (hb.trans hεhalf)
end SmoothObstruction.ManifoldCoordinates

end

end OAI
