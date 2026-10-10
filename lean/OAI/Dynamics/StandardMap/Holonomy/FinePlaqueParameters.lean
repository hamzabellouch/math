import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Holonomy.ConeIntervalDistortion

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma fine_plaque_parameters {χ τ : ℝ} (hχ : 0<χ) (hτ : 0<τ) :
    ∃ ε δ : ℝ, 0<ε ∧ 0<δ ∧ δ≤1/2 ∧ Real.exp (-χ+ε)+δ<1 ∧
      Real.exp (2*ε)*(Real.exp (-χ+ε)+δ)<1 ∧
      Real.exp (-χ+ε)*δ/(1-Real.exp (-χ+ε))≤τ := by
  let ε := χ/10
  let ℓ := Real.exp (-χ+ε)
  let ρ := Real.exp (-χ/2)
  have hε : 0<ε := by dsimp [ε]; positivity
  have hℓ0 : 0<ℓ := Real.exp_pos _
  have hℓρ : ℓ<ρ := Real.exp_lt_exp.mpr (by dsimp [ε]; linarith)
  have hρ1 : ρ<1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hℓ1 : ℓ<1 := hℓρ.trans hρ1
  let δ := min ((ρ-ℓ)/2) (min (τ*(1-ℓ)/2) (1/2))
  have hδ : 0<δ := lt_min (by linarith) (lt_min (by positivity) (by norm_num))
  have hdρ : δ≤(ρ-ℓ)/2 := min_le_left _ _
  have hdτ : δ≤τ*(1-ℓ)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hd1 : δ≤1/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hqρ : ℓ+δ≤ρ := by linarith
  have hslow : Real.exp (2*ε)*ρ<1 := by
    rw [←Real.exp_add]
    exact Real.exp_lt_one_iff.mpr (by dsimp [ε]; linarith)
  refine ⟨ε,δ,hε,hδ,hd1,hqρ.trans_lt hρ1,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_left hqρ (Real.exp_pos _).le).trans_lt hslow
  · apply (div_le_iff₀ (sub_pos.mpr hℓ1)).mpr
    have hb := mul_le_mul_of_nonneg_right hℓ1.le hδ.le
    nlinarith

lemma fineStableGraph_slope (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    (s t : ℝ) :
    |fineStableGraph k χ ε δ hδ hq w hw s-fineStableGraph k χ ε δ hδ hq w hw t|≤
      (Real.exp (-χ+ε)*δ/(1-Real.exp (-χ+ε)))*|s-t| :=
  graph_slope_bound (fineLocalRecurrence k χ ε δ hδ w hw).extend hq s t

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma fine_holonomy_parameters {χ τ : ℝ} (hχ : 0<χ) (hτ : 0<τ) :
    ∃ ε δ : ℝ, 0<ε ∧ 0<δ ∧ δ≤1/2 ∧ Real.exp (-χ+ε)+δ<1 ∧
      Real.exp (4*ε)*(Real.exp (-χ+ε)+δ)<1 ∧
      Real.exp (-χ+ε)*δ/(1-Real.exp (-χ+ε))≤τ := by
  let ε := χ/10
  let ℓ := Real.exp (-χ+ε)
  let ρ := Real.exp (-χ/2)
  have hε : 0<ε := by dsimp [ε]; positivity
  have hℓ0 : 0<ℓ := Real.exp_pos _
  have hℓρ : ℓ<ρ := Real.exp_lt_exp.mpr (by dsimp [ε]; linarith)
  have hρ1 : ρ<1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hℓ1 : ℓ<1 := hℓρ.trans hρ1
  let δ := min ((ρ-ℓ)/2) (min (τ*(1-ℓ)/2) (1/2))
  have hδ : 0<δ := lt_min (by linarith) (lt_min (by positivity) (by norm_num))
  have hdρ : δ≤(ρ-ℓ)/2 := min_le_left _ _
  have hdτ : δ≤τ*(1-ℓ)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hd1 : δ≤1/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hqρ : ℓ+δ≤ρ := by linarith
  have hslow : Real.exp (4*ε)*ρ<1 := by
    rw [←Real.exp_add]
    exact Real.exp_lt_one_iff.mpr (by dsimp [ε]; linarith)
  refine ⟨ε,δ,hε,hδ,hd1,hqρ.trans_lt hρ1,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_left hqρ (Real.exp_pos _).le).trans_lt hslow
  · apply (div_le_iff₀ (sub_pos.mpr hℓ1)).mpr
    have hb := mul_le_mul_of_nonneg_right hℓ1.le hδ.le
    nlinarith

lemma NonlinearStable.Recurrence.orbit_solution {ℓ δ : ℝ≥0} (r : Recurrence ℓ δ)
    (h : ℓ+δ<1) (s : ℝ) (n : ℕ) : r.orbit (r.solution h s 0) n=r.solution h s n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Recurrence.orbit,ih,solution_orbit]

lemma fine_central_orbit_decay (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {v : Plane} {s : ℝ} (hs : |s|≤1/12)
    (he : w+fineFrame k χ ε δ (complexProjection w) v=fineStableCurve k χ ε δ hδ hq w hw s)
    (n : ℕ) : ‖(fineLocalRecurrence k χ ε δ hδ w hw).extend.orbit v n‖≤
      (Real.exp (-χ+ε)+δ)^n/12 := by
  let r := fineLocalRecurrence k χ ε δ hδ w hw
  have hs' : |s|≤1 := hs.trans (by norm_num)
  have hv : v=r.extend.solution hq s 0 := by
    have hh := congrArg (fun p => fineCoordinate k χ ε δ w p 0) he
    rw [fineCoordinate_initial k χ ε hδ w (hw 0),fineStableCoordinate k χ ε δ hδ hq w hw hs'] at hh
    exact hh
  rw [hv,r.extend.orbit_solution hq]
  have hdec : ‖r.extend.solution hq s n‖≤(Real.exp (-χ+ε)+δ)^n*|s| := by
    have hh := solution_exponential_contraction r.extend hq s 0 n
    rw [solution_zero r.extend hq] at hh
    change ‖r.extend.solution hq s n-0‖≤(Real.exp (-χ+ε)+δ)^n*|s-0| at hh
    simpa only [sub_zero] using hh
  exact hdec.trans ((mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring))

theorem fine_stable_matching_local_bound (k : ℝ) (hk : 0≤k) (χ ε δ : ℝ)
    (hε : 0≤ε) (hδ : 0<δ) (hδ' : δ≤1/2) (hq : Real.exp (-χ+ε)+δ<1)
    (hslow : Real.exp (4*ε)*(Real.exp (-χ+ε)+δ)<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    (p q V : Plane) (hc : |V.1|≤|V.2|) (hV : V.2≠0)
    (S : Set ℝ) (H : ℝ → ℝ) {t₀ : ℝ} (ht₀ : t₀∈S) (hH : ContinuousWithinAt H S t₀)
    {s₀ s₁ : ℝ} (hs₀ : |s₀|≤1/12) (hs₁ : |s₁|≤1/12)
    (hp₀ : w+fineFrame k χ ε δ (complexProjection w) (p+t₀•V)=fineStableCurve k χ ε δ hδ hq w hw s₀)
    (hq₀ : w+fineFrame k χ ε δ (complexProjection w) (q+H t₀•V)=fineStableCurve k χ ε δ hδ hq w hw s₁)
    (hmatch : ∀ t∈S, ∃ (v : ℂ)
      (hv : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] v))) (s u : ℝ),
      |s|≤1 ∧ |u|≤1 ∧
      w+fineFrame k χ ε δ (complexProjection w) (p+t•V)=fineStableCurve k χ ε δ hδ hq v hv s ∧
      w+fineFrame k χ ε δ (complexProjection w) (q+H t•V)=fineStableCurve k χ ε δ hδ hq v hv u) :
    ∀ᶠ t in 𝓝[S] t₀, |H t-H t₀|≤(2*Real.exp (8*δ/(1-(Real.exp (-χ+ε)+δ))))* |t-t₀| := by
  let r := fineLocalRecurrence k χ ε δ hδ w hw
  let D (n : ℕ) := fineRemainderDerivative k χ ε δ ((standardLift k)^[n] w)
  let a := Real.exp (2*ε)
  let b := Real.exp (-χ+ε)+δ
  have hb : 0<b := add_pos (Real.exp_pos _) hδ
  have hscale := fineScale_pos k ε hδ
  have hab : a*b<1 := (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (by linarith : 2*ε≤4*ε)) hb.le).trans_lt hslow
  have haρ : a*(a*b)<1 := by
    have he : a*(a*b)=Real.exp (4*ε)*b := by
      dsimp only [a]
      rw [←mul_assoc,←Real.exp_add]
      congr 2
      ring
    rwa [he]
  obtain ⟨M,hM,hstep⟩ := fine_extended_step_bound k hk χ ε δ hε hδ w hw
  have hsmall (n : ℕ) (v : Plane) (_ : ‖v‖≤1) : ‖D n v‖≤δ*‖v‖ := by
    have hh := fineRemainderDerivative_lipschitz k χ ε hδ ((standardLift k)^[n] w)
      (hw n) (fine_regular_lift_next k χ ε w hw n) v 0
    simpa only [fineRemainderDerivative_zero,sub_zero] using hh
  have htrack (t : ℝ) (ht : t∈S) (N : ℕ)
      (hP : ∀ n : ℕ,n≤N → ‖r.extend.orbit (p+t•V) n‖≤1/3)
      (hQ : ∀ n : ℕ,n≤N → ‖r.extend.orbit (q+H t•V) n‖≤1/3) :
      ‖r.extend.orbit (p+t•V) N-r.extend.orbit (q+H t•V) N‖≤
        ((4*fineScale k ε δ)/(100*codingRadius k χ ε δ (complexProjection w)))*(a*b)^N := by
    have htp : p+t•V∈r.extend.trappedBox N := fun n hn => (hP n hn).trans (by norm_num)
    have htq : q+H t•V∈r.extend.trappedBox N := fun n hn => (hQ n hn).trans (by norm_num)
    rw [←r.trueOrbit_eq_extend htp le_rfl,←r.trueOrbit_eq_extend htq le_rfl]
    rw [fine_trueOrbit,fine_trueOrbit]
    obtain ⟨v,hv,s,u,hs,hu,hps,hqu⟩ := hmatch t ht
    have hd (n : ℕ) :
        ‖(standardLift k)^[n] (w+fineFrame k χ ε δ (complexProjection w) (p+t•V))-
          (standardLift k)^[n] (w+fineFrame k χ ε δ (complexProjection w) (q+H t•V))‖≤
          (4*fineScale k ε δ)*b^n := by
      rw [hps,hqu]
      have hh := fineStableCurve_contraction k χ ε δ hδ hq v hv hs hu n
      have hsu : |s-u|≤2 := (abs_sub _ _).trans (by linarith)
      have hm := mul_le_mul_of_nonneg_left hsu (by positivity : 0≤(2*fineScale k ε δ)*b^n)
      exact hh.trans (hm.trans_eq (by ring))
    exact fineCoordinate_tracking_rate k χ ε δ hδ w _ _ hw
      (by positivity [fineScale_pos k ε hδ]) hb.le hd N
  exact r.holonomy_local_bound hq hδ' D (fun n v => hasFDerivAt_fineRemainder k χ ε δ _ v)
    hsmall p q V hc hV S H ht₀ hH hM (Real.exp_pos _) hb.le hq.le
    (mul_nonneg (Real.exp_pos _).le hb.le) hab haρ hstep
    (fine_central_orbit_decay k χ ε δ hδ hq w hw hs₀ hp₀)
    (fine_central_orbit_decay k χ ε δ hδ hq w hw hs₁ hq₀) htrack

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

theorem null_image_of_pointwise_local_bound {S : Set ℝ} {H : ℝ → ℝ} {K : ℝ} (hK : 0≤K)
    (h : ∀ x∈S, ∀ᶠ y in 𝓝[S] x, |H y-H x| ≤ K*|y-x|)
    {Z : Set ℝ} (hZS : Z⊆S) (hZ : volume Z=0) : volume (H '' Z)=0 := by
  classical
  let A (n : ℕ) : Set ℝ := {x | x∈S ∧ |H x| ≤ (n : ℝ) ∧
    ∀ y∈S, |y-x| < 1/((n : ℝ)+1) → |H y-H x| ≤ K*|y-x|}
  have hcover : S⊆⋃ n : ℕ,A n := by
    intro x hx
    obtain ⟨ε,hε,hball⟩ := Metric.mem_nhdsWithin_iff.mp (h x hx)
    obtain ⟨n,hn⟩ := exists_nat_gt (max |H x| (1/ε))
    have hbn : |H x| ≤ (n : ℝ) := ((le_max_left _ _).trans_lt hn).le
    have hεn : 1/((n : ℝ)+1)<ε := by
      have he : 1/ε<(n : ℝ) := (le_max_right _ _).trans_lt hn
      have hh : 1<(n : ℝ)*ε := (div_lt_iff₀ hε).mp he
      apply (div_lt_iff₀ (by positivity : 0<(n : ℝ)+1)).mpr
      nlinarith
    refine mem_iUnion.mpr ⟨n,hx,hbn,fun y hy hxy => ?_⟩
    exact hball ⟨by simpa only [Metric.mem_ball,Real.dist_eq] using hxy.trans hεn,hy⟩
  have hLip (n : ℕ) : LipschitzOnWith
      ⟨max K (2*(n : ℝ)*((n : ℝ)+1)), hK.trans (le_max_left _ _)⟩ H (A n) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    change |H x-H y| ≤ max K (2*(n : ℝ)*((n : ℝ)+1))*|x-y|
    by_cases hxy : |x-y| < 1/((n : ℝ)+1)
    · exact (hy.2.2 x hx.1 hxy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
    · have hd : 1/((n : ℝ)+1)≤|x-y| := le_of_not_gt hxy
      have hprod : 1≤|x-y| *((n : ℝ)+1) := (div_le_iff₀ (by positivity)).mp hd
      have hleft : |H x-H y| ≤ 2*(n : ℝ) := (abs_sub _ _).trans (by linarith [hx.2.1,hy.2.1])
      have hm := mul_le_mul_of_nonneg_left hprod (by positivity : 0≤2*(n : ℝ))
      apply hleft.trans
      apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))
      nlinarith
  have hpieces (n : ℕ) : volume (H '' (Z∩A n))=0 := by
    have hz : volume (Z∩A n)=0 := measure_mono_null inter_subset_left hZ
    have hl := ((hLip n).mono (show Z∩A n⊆A n from inter_subset_right)).hausdorffMeasure_image_le (by norm_num : (0:ℝ)≤1)
    rw [hausdorffMeasure_real,hz,mul_zero] at hl
    exact bot_unique hl
  have hsub : H '' Z⊆⋃ n : ℕ,H '' (Z∩A n) := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨n,hn⟩ := mem_iUnion.mp (hcover (hZS hx))
    exact mem_iUnion.mpr ⟨n,x,⟨hx,hn⟩,rfl⟩
  exact measure_mono_null hsub (measure_iUnion_null hpieces)

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma fine_affine_coordinates (k χ ε δ : ℝ) (hδ : 0<δ) (w p V : ℂ)
    (hw : FineRegular k χ ε (complexProjection w)) (t : ℝ) :
    w+fineFrame k χ ε δ (complexProjection w)
      (fineInverse k χ ε δ (complexProjection w) (p-w)+t•fineInverse k χ ε δ (complexProjection w) V)=
      p+t•V := by
  rw [map_add,map_smul,fineFrame_inverse k χ ε hδ _ hw.1,
    fineFrame_inverse k χ ε hδ _ hw.1]
  abel

theorem actual_stable_holonomy_null_image (k : ℝ) (hk : 0≤k) (χ ε δ : ℝ)
    (hε : 0≤ε) (hδ : 0<δ) (hδ' : δ≤1/2) (hq : Real.exp (-χ+ε)+δ<1)
    (hslow : Real.exp (4*ε)*(Real.exp (-χ+ε)+δ)<1)
    (P Q W : ℂ) (S : Set ℝ) (H : ℝ → ℝ) (hH : ContinuousOn H S)
    (hmatch : ∀ t∈S, ∃ (v : ℂ)
      (hv : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] v))) (s u : ℝ),
      |s|≤1/12 ∧ |u|≤1/12 ∧
      |(fineInverse k χ ε δ (complexProjection v) W).1|≤
        |(fineInverse k χ ε δ (complexProjection v) W).2| ∧
      (fineInverse k χ ε δ (complexProjection v) W).2≠0 ∧
      P+t•W=fineStableCurve k χ ε δ hδ hq v hv s ∧
      Q+H t•W=fineStableCurve k χ ε δ hδ hq v hv u)
    {Z : Set ℝ} (hZS : Z⊆S) (hZ : volume Z=0) : volume (H '' Z)=0 := by
  apply null_image_of_pointwise_local_bound (K := 2*Real.exp (8*δ/(1-(Real.exp (-χ+ε)+δ)))) (by positivity) _ hZS hZ
  intro t ht
  obtain ⟨v,hv,s,u,hs,hu,hcone,hnonzero,hleft,hright⟩ := hmatch t ht
  let I := fineInverse k χ ε δ (complexProjection v)
  have he (p : ℂ) (t : ℝ) : v+fineFrame k χ ε δ (complexProjection v) (I (p-v)+t•I W)=p+t•W :=
    fine_affine_coordinates k χ ε δ hδ v p W (hv 0) t
  have hleft' : v+fineFrame k χ ε δ (complexProjection v) (I (P-v)+t•I W)=
      fineStableCurve k χ ε δ hδ hq v hv s := (he P t).trans hleft
  have hright' : v+fineFrame k χ ε δ (complexProjection v) (I (Q-v)+H t•I W)=
      fineStableCurve k χ ε δ hδ hq v hv u := (he Q (H t)).trans hright
  apply fine_stable_matching_local_bound k hk χ ε δ hε hδ hδ' hq hslow v hv
    (I (P-v)) (I (Q-v)) (I W) hcone hnonzero S H ht (hH t ht) hs hu hleft' hright'
  intro t' ht'
  obtain ⟨v',hv',s',u',hs',hu',_,_,hleft'',hright''⟩ := hmatch t' ht'
  exact ⟨v',hv',s',u',hs'.trans (by norm_num),hu'.trans (by norm_num),
    (he P t').trans hleft'',(he Q (H t')).trans hright''⟩

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma strictMono_of_linear_error {f : ℝ → ℝ} {κ : ℝ} (hκ : κ<1)
    (h : ∀ s t : ℝ, |f s-f t-(s-t)|≤κ*|s-t|) : StrictMono f := by
  intro s t hst
  have hh := (abs_le.mp (h t s)).1
  rw [abs_of_pos (sub_pos.mpr hst)] at hh
  nlinarith

theorem compact_graph_crossing {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (r : ℝ) (hr : 0<r) (F : X → ℝ → Plane)
    (hF : Continuous (fun p : X×Icc (-r) r => F p.1 p.2))
    (he : ∀ x s t, |(F x s).1-(F x t).1-(s-t)|≤(1/4)*|s-t|)
    (hzero : ∀ x, |(F x 0).1|≤r/4) :
    ∃ σ : (X×Icc (-r/2) (r/2)) → Icc (-r) r, Continuous σ ∧
      ∀ v, (F v.1 (σ v)).1=(v.2 : ℝ) := by
  classical
  have hm (x : X) : StrictMono (fun s => (F x s).1) := strictMono_of_linear_error (by norm_num) (he x)
  have hf (x : X) : ContinuousOn (fun s => (F x s).1) (Icc (-r) r) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (hF.comp (continuous_const.prodMk continuous_id)).fst
  have hend (x : X) : (F x (-r)).1≤-r/2 ∧ r/2≤(F x r).1 := by
    have hl := (abs_le.mp (he x (-r) 0)).2
    have hu := (abs_le.mp (he x r 0)).1
    have hz := abs_le.mp (hzero x)
    simp only [sub_zero,abs_neg,abs_of_pos hr] at hl hu
    constructor <;> linarith
  have hex (v : X×Icc (-r/2) (r/2)) : ∃ s : Icc (-r) r, (F v.1 s).1=(v.2 : ℝ) := by
    obtain ⟨s,hs,hs'⟩ := intermediate_value_Icc (by linarith : -r≤r) (hf v.1)
      ⟨(hend v.1).1.trans v.2.property.1,v.2.property.2.trans (hend v.1).2⟩
    exact ⟨⟨s,hs⟩,hs'⟩
  choose σ hσ using hex
  let G : X×Icc (-r) r → X×ℝ := fun p => (p.1,(F p.1 p.2).1)
  have hGc : Continuous G := continuous_fst.prodMk hF.fst
  have hGi : Function.Injective G := by
    rintro ⟨x,s⟩ ⟨y,t⟩ heq
    have hxy : x=y := congrArg Prod.fst heq
    subst y
    have hst : (s : ℝ)=(t : ℝ) := (hm x).injective (congrArg Prod.snd heq)
    exact Prod.ext rfl (Subtype.ext hst)
  have hemb := hGc.isClosedEmbedding hGi |>.isEmbedding
  have hpair : Continuous (fun v : X×Icc (-r/2) (r/2) => (v.1,σ v)) := by
    apply hemb.continuous_iff.mpr
    have heq : G ∘ (fun v : X×Icc (-r/2) (r/2) => (v.1,σ v))=
        (fun v => (v.1,(v.2 : ℝ))) := by
      funext v; exact Prod.ext rfl (hσ v)
    rw [heq]
    exact continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  exact ⟨σ,hpair.snd,hσ⟩

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma fine_graph_pair_bound (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (v : ℂ) (hv : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] v))) (s t : ℝ) :
    ‖((s,fineStableGraph k χ ε δ hδ hq v hv s) : Plane)-
      (t,fineStableGraph k χ ε δ hδ hq v hv t)‖≤|s-t| := by
  have hg := (graph_lipschitz (fineLocalRecurrence k χ ε δ hδ v hv).extend hq).dist_le_mul s t
  change max |s-t| |fineStableGraph k χ ε δ hδ hq v hv s-fineStableGraph k χ ε δ hδ hq v hv t|≤|s-t|
  exact max_le le_rfl (by simpa only [Real.dist_eq,NNReal.coe_one,one_mul,fineStableGraph] using hg)

noncomputable def finePlaqueInChart (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w v : ℂ) (hv : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] v)))
    (s : ℝ) : Plane :=
  fineInverse k χ ε δ (complexProjection w) (fineStableCurve k χ ε δ hδ hq v hv s-w)

lemma fine_plaque_linear_error (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w v : ℂ) (hv : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] v)))
    (hclose : ‖(fineInverse k χ ε δ (complexProjection w)).comp (fineFrame k χ ε δ (complexProjection v))-
      ContinuousLinearMap.id ℝ Plane‖≤1/4) (s t : ℝ) :
    |(finePlaqueInChart k χ ε δ hδ hq w v hv s).1-
      (finePlaqueInChart k χ ε δ hδ hq w v hv t).1-(s-t)|≤(1/4)*|s-t| := by
  let I := fineInverse k χ ε δ (complexProjection w)
  let F := fineFrame k χ ε δ (complexProjection v)
  let u : Plane := (s,fineStableGraph k χ ε δ hδ hq v hv s)-(t,fineStableGraph k χ ε δ hδ hq v hv t)
  have he : (finePlaqueInChart k χ ε δ hδ hq w v hv s).1-
      (finePlaqueInChart k χ ε δ hδ hq w v hv t).1-(s-t)=
      (((I.comp F)-ContinuousLinearMap.id ℝ Plane) u).1 := by
    change (I (v+F (s,fineStableGraph k χ ε δ hδ hq v hv s)-w)).1-
      (I (v+F (t,fineStableGraph k χ ε δ hδ hq v hv t)-w)).1-(s-t)=_
    simp only [map_sub,map_add,Prod.fst_add,Prod.fst_sub,sub_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,u]
    ring
  rw [he]
  exact (norm_fst_le _).trans ((ContinuousLinearMap.le_opNorm _ _).trans
    ((mul_le_mul_of_nonneg_right hclose (norm_nonneg u)).trans
      (mul_le_mul_of_nonneg_left (fine_graph_pair_bound k χ ε δ hδ hq v hv s t) (by norm_num))))

lemma fine_plaque_crossing_unique (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w v : ℂ) (hv : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] v)))
    (hclose : ‖(fineInverse k χ ε δ (complexProjection w)).comp (fineFrame k χ ε δ (complexProjection v))-
      ContinuousLinearMap.id ℝ Plane‖≤1/4) :
    Function.Injective (fun s => (finePlaqueInChart k χ ε δ hδ hq w v hv s).1) :=
  (strictMono_of_linear_error (by norm_num) (fine_plaque_linear_error k χ ε δ hδ hq w v hv hclose)).injective

theorem fine_compact_graph_crossing {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (v : X → ℂ) (hvc : Continuous v)
    (hv : ∀ x, ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] (v x))))
    (hdata : ∀ n : ℕ, Continuous (fun x => lyapunovChartData k χ ε
      (complexProjection ((standardLift k)^[n] (v x)))))
    {r : ℝ} (hr : 0<r) (hr1 : r≤1)
    (hclose : ∀ x, ‖(fineInverse k χ ε δ (complexProjection w)).comp (fineFrame k χ ε δ (complexProjection (v x)))-
      ContinuousLinearMap.id ℝ Plane‖≤1/4)
    (hcentre : ∀ x, |(fineInverse k χ ε δ (complexProjection w) (v x-w)).1|≤r/4) :
    ∃ σ : (X×Icc (-r/2) (r/2)) → Icc (-r) r, Continuous σ ∧ ∀ p : X×Icc (-r/2) (r/2),
      (finePlaqueInChart k χ ε δ hδ hq w (v p.1) (hv p.1) (σ p)).1=(p.2 : ℝ) := by
  let F (x : X) (s : ℝ) := finePlaqueInChart k χ ε δ hδ hq w (v x) (hv x) s
  have hc0 := continuous_fineStableCurve_family k χ ε δ hδ hq v hvc hv hdata
  let ι : Icc (-r) r → Icc (-1 : ℝ) 1 := fun s => ⟨s,⟨by linarith [s.property.1],s.property.2.trans hr1⟩⟩
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  have hc : Continuous (fun p : X×Icc (-r) r => F p.1 p.2) := by
    exact (fineInverse k χ ε δ (complexProjection w)).continuous.comp
      ((hc0.comp (continuous_fst.prodMk (hι.comp continuous_snd))).sub continuous_const)
  apply compact_graph_crossing r hr F hc (fun x => fine_plaque_linear_error k χ ε δ hδ hq w (v x) (hv x) (hclose x))
  intro x
  simpa only [F,finePlaqueInChart,fineStableCurve_zero] using hcentre x

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

theorem fine_small_crossings_coincide (k χ ε δ : ℝ) (hδ : 0<δ)
    (hq : Real.exp (-χ+ε)+δ<1) (hslow : Real.exp (2*ε)*(Real.exp (-χ+ε)+δ)≤1)
    (w v v' : ℂ)
    (hv : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] v)))
    (hv' : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] v')))
    {r R : ℝ} (hr : 0<r) (hr1 : r≤1) (hR : 0<R)
    (hRv : R≤codingRadius k χ ε δ (complexProjection v))
    (hsize : (4*fineScale k ε δ*r)/(100*R)+r≤1)
    (hclose : ‖(fineInverse k χ ε δ (complexProjection w)).comp (fineFrame k χ ε δ (complexProjection v))-
      ContinuousLinearMap.id ℝ Plane‖≤1/4)
    {s t s' t' : ℝ} (hs : |s|≤r) (ht : |t|≤r) (hs' : |s'|≤r) (ht' : |t'|≤r)
    (hmeet : fineStableCurve k χ ε δ hδ hq v hv s=fineStableCurve k χ ε δ hδ hq v' hv' s')
    (hcross : (finePlaqueInChart k χ ε δ hδ hq w v hv t).1=
      (finePlaqueInChart k χ ε δ hδ hq w v' hv' t').1) :
    fineStableCurve k χ ε δ hδ hq v hv t=fineStableCurve k χ ε δ hδ hq v' hv' t' := by
  let p := fineStableCurve k χ ε δ hδ hq v' hv' t'
  let p₀ := fineStableCurve k χ ε δ hδ hq v hv s
  have hscale := fineScale_pos k ε hδ
  have hq0 : 0≤Real.exp (-χ+ε)+δ := by positivity
  have htrack (n : ℕ) : ‖(standardLift k)^[n] p-(standardLift k)^[n] p₀‖≤
      ((2*fineScale k ε δ)*|t'-s'|)*(Real.exp (-χ+ε)+δ)^n := by
    dsimp only [p,p₀]
    rw [hmeet]
    exact (fineStableCurve_contraction k χ ε δ hδ hq v' hv' (ht'.trans hr1) (hs'.trans hr1) n).trans_eq (by ring)
  have hdiff : |t'-s'|≤2*r := (abs_sub _ _).trans (by linarith)
  have hdist (n : ℕ) : ‖fineCoordinate k χ ε δ v p n-fineCoordinate k χ ε δ v p₀ n‖≤
      (4*fineScale k ε δ*r)/(100*R) := by
    have hd := fineCoordinate_tracking_difference k χ ε δ hδ v p p₀ hv (by positivity) hq0 hslow htrack n
    apply hd.trans
    calc
      _ ≤ (4*fineScale k ε δ*r)/(100*codingRadius k χ ε δ (complexProjection v)) :=
        div_le_div_of_nonneg_right (by nlinarith only [hdiff,hscale])
          (by positivity [codingRadius_pos k χ ε hδ (complexProjection v)])
      _ ≤ _ := div_le_div_of_nonneg_left
        (mul_nonneg (mul_nonneg (by norm_num) hscale.le) hr.le) (by positivity : 0<100*R)
        (mul_le_mul_of_nonneg_left hRv (by norm_num))
  have hp (n : ℕ) : ‖fineCoordinate k χ ε δ v p n‖≤1 := by
    have hc : ‖fineCoordinate k χ ε δ v p₀ n‖≤r :=
      (fineStableCoordinate_bound k χ ε δ hδ hq v hv (hs.trans hr1) n).trans hs
    have hh := norm_add_le (fineCoordinate k χ ε δ v p n-fineCoordinate k χ ε δ v p₀ n)
      (fineCoordinate k χ ε δ v p₀ n)
    rw [sub_add_cancel] at hh
    exact hh.trans ((add_le_add (hdist n) hc).trans hsize)
  have hu := fineStableCurve_unique k χ ε δ hδ hq v p hv hp
  let a := (fineCoordinate k χ ε δ v p 0).1
  have hca : (finePlaqueInChart k χ ε δ hδ hq w v hv t).1=
      (finePlaqueInChart k χ ε δ hδ hq w v hv a).1 := by
    apply hcross.trans
    change (fineInverse k χ ε δ (complexProjection w) (p-w)).1=_
    rw [hu]
    rfl
  have hta : t=a := (fine_plaque_crossing_unique k χ ε δ hδ hq w v hv hclose).injOn
    (s := Icc (-1) 1) (abs_le.mp (ht.trans hr1))
    (abs_le.mp ((norm_fst_le _).trans (hp 0))) hca
  rw [hta]
  exact hu.symm

end StandardMapEntropy

end
end

end OAI
