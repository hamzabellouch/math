import OAI.Analysis.NodalLength.ProfileTests

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace

namespace SharpNodal.Profiles

variable {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]

def basisProfile (ell : countableBasis X → EReal) (x : X) : EReal :=
  ⨅ i, ⨅ (_ : x∈i.val), ell i

lemma basisProfile_le (ell : countableBasis X → EReal) (i : countableBasis X)
    {x : X} (hx : x∈i.val) : basisProfile ell x≤ell i :=
  (iInf_le_of_le i (iInf_le_of_le hx le_rfl))

lemma basisProfile_lt_iff (ell : countableBasis X → EReal) (x : X) (a : EReal) :
    basisProfile ell x<a ↔ ∃ i : countableBasis X, x∈i.val ∧ ell i<a := by
  simp only [basisProfile, iInf_lt_iff, exists_prop]

lemma upperSemicontinuous_basisProfile (ell : countableBasis X → EReal) :
    UpperSemicontinuous (basisProfile ell) := by
  intro x a hxa
  obtain ⟨i, hxi, hia⟩ := (basisProfile_lt_iff ell x a).mp hxa
  filter_upwards [(isOpen_of_mem_countableBasis i.property).mem_nhds hxi] with y hy
  exact (basisProfile_le ell i hy).trans_lt hia

lemma basisProfile_nonpos (ell : countableBasis X → EReal) (hell : ∀ i, ell i≤0)
    (x : X) : basisProfile ell x≤0 := by
  obtain ⟨G, hG, hxG, _⟩ := (isBasis_countableBasis X).exists_subset_of_mem_open
    (mem_univ x) isOpen_univ
  exact (basisProfile_le ell ⟨G,hG⟩ hxG).trans (hell _)

theorem extract_basis_rates [MeasurableSpace X]
    (μ : ℕ → Measure X) (S : ℕ → ℝ) :
    ∃ (ell : countableBasis X → EReal) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ i : countableBasis X,
        Tendsto (fun j => logRate (S (φ j)) (μ (φ j) i.val)) atTop (𝓝 (ell i)) := by
  let z : ℕ → (countableBasis X → EReal) := fun j i => logRate (S j) (μ j i.val)
  obtain ⟨ell, φ, hφ, hz⟩ := CompactSpace.tendsto_subseq z
  refine ⟨ell, φ, hφ, fun i => ?_⟩
  exact (continuous_apply i).tendsto ell |>.comp hz

lemma basis_rates_nonpos [MeasurableSpace X] {μ : ℕ → Measure X} {S : ℕ → ℝ}
    {ell : countableBasis X → EReal} {φ : ℕ → ℕ}
    (hS : ∀ j, 0<S j) (hnorm : ∀ j, μ j univ≤1)
    (hlim : ∀ i : countableBasis X,
      Tendsto (fun j => logRate (S (φ j)) (μ (φ j) i.val)) atTop (𝓝 (ell i))) :
    ∀ i, ell i≤0 := by
  intro i
  apply le_of_tendsto (hlim i)
  filter_upwards [] with j
  change logRate (S (φ j)) (μ (φ j) i.val) ≤ (0 : ℝ)
  apply (logRate_le_iff (hS _) _).mpr
  simpa using (measure_mono (subset_univ i.val)).trans (hnorm (φ j))

lemma open_profile_lower [MeasurableSpace X] {μ : ℕ → Measure X} {S : ℕ → ℝ}
    {ell : countableBasis X → EReal}
    (hS : ∀ j, 0<S j)
    (hlim : ∀ i : countableBasis X,
      Tendsto (fun j => logRate (S j) (μ j i.val)) atTop (𝓝 (ell i)))
    {G : Set X} (hG : IsOpen G) :
    (⨆ x∈G, basisProfile ell x)≤liminf (fun j => logRate (S j) (μ j G)) atTop := by
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  obtain ⟨U, hU, hxU, hUG⟩ := (isBasis_countableBasis X).exists_subset_of_mem_open hx hG
  let i : countableBasis X := ⟨U,hU⟩
  apply (basisProfile_le ell i hxU).trans
  rw [← (hlim i).liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun j => logRate_mono (hS j) (measure_mono hUG))

lemma compact_profile_upper [MeasurableSpace X] {μ : ℕ → Measure X} {S : ℕ → ℝ}
    {ell : countableBasis X → EReal}
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop)
    (hlim : ∀ i : countableBasis X,
      Tendsto (fun j => logRate (S j) (μ j i.val)) atTop (𝓝 (ell i)))
    {F : Set X} (hF : IsCompact F) :
    limsup (fun j => logRate (S j) (μ j F)) atTop≤⨆ x∈F, basisProfile ell x := by
  classical
  by_contra hn
  obtain ⟨b, hVb, hbL⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
  obtain ⟨a, hVa, hab⟩ := EReal.lt_iff_exists_real_btwn.mp hVb
  have hab' : a<b := by exact_mod_cast hab
  let I := {i : countableBasis X // ell i<(a:EReal)}
  let U : I → Set X := fun i => i.val.val
  have hcover : F⊆⋃ i, U i := by
    intro x hx
    have hxa : basisProfile ell x<(a:EReal) :=
      (le_iSup₂_of_le x hx le_rfl).trans_lt hVa
    obtain ⟨i, hxi, hia⟩ := (basisProfile_lt_iff ell x a).mp hxa
    exact mem_iUnion.mpr ⟨⟨i,hia⟩,hxi⟩
  obtain ⟨t, ht⟩ := hF.elim_finite_subcover U
    (fun i => isOpen_of_mem_countableBasis i.val.property) hcover
  have hterms : ∀ᶠ j in atTop, ∀ i∈t,
      μ j (U i)≤ENNReal.ofReal (Real.exp (2*S j*a)) := by
    apply (eventually_all_finset t).mpr
    intro i hi
    filter_upwards [(hlim i.val).eventually (gt_mem_nhds i.property)] with j hj
    exact ((logRate_lt_iff (hSpos j) _).mp hj).le
  have hc : 0<(t.card:ℝ)+1 := by positivity
  have hgap := exponential_gap hS hab' hc
  have hbound : ∀ᶠ j in atTop, logRate (S j) (μ j F)≤(b:EReal) := by
    filter_upwards [hterms, hgap] with j hj hg
    apply (logRate_le_iff (hSpos j) _).mpr
    have hsum : μ j F≤∑ i∈t, μ j (U i) :=
      (measure_mono ht).trans (measure_biUnion_finset_le t U)
    apply hsum.trans
    calc
      (∑ i∈t, μ j (U i)) ≤ ∑ _i∈t, ENNReal.ofReal (Real.exp (2*S j*a)) :=
        Finset.sum_le_sum fun i hi => hj i hi
      _ = (t.card:ℝ≥0∞)*ENNReal.ofReal (Real.exp (2*S j*a)) := by simp
      _ ≤ ENNReal.ofReal ((t.card:ℝ)+1)*ENNReal.ofReal (Real.exp (2*S j*a)) := by
        gcongr
        exact_mod_cast (le_add_of_nonneg_right (show (0:ℝ)≤1 by norm_num) :
          (t.card:ℝ)≤(t.card:ℝ)+1)
      _ = ENNReal.ofReal (((t.card:ℝ)+1)*Real.exp (2*S j*a)) :=
        (ENNReal.ofReal_mul hc.le).symm
      _ ≤ ENNReal.ofReal (Real.exp (2*S j*b)) := ENNReal.ofReal_le_ofReal hg.le
  exact (not_le_of_gt hbL) (limsup_le_of_le (by isBoundedDefault) hbound)

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set
namespace SharpNodal.Profiles
open Carleman

lemma upper_test_of_maximum {V : Plane → EReal} {q : Plane → ℝ} {F : Set Plane}
    {x₀ : Plane} (hx₀ : x₀∈interior F) (hfinite : V x₀≠⊤ ∧ V x₀≠⊥)
    (hmax : IsMaxOn (fun x => V x+((-q x:ℝ):EReal)) F x₀) :
    IsUpperTest V (fun x => q x+(V x₀).toReal-q x₀) x₀ := by
  have hv := EReal.coe_toReal hfinite.1 hfinite.2
  refine ⟨?_, ?_⟩
  · simp only [add_sub_cancel_left, hv]
  · filter_upwards [mem_interior_iff_mem_nhds.mp hx₀] with x hx
    apply (EReal.addLECancellable_coe (-q x)).add_le_add_iff_right.mp
    have hh : V x+((-q x:ℝ):EReal) ≤ V x₀+((-q x₀:ℝ):EReal) := hmax hx
    rw [← hv, ← EReal.coe_add] at hh
    convert hh using 1
    rw [← EReal.coe_add]
    congr 1
    ring

lemma negative_trace_coordinate {A : BilinearForm} (hA : formTrace A<0) :
    ∃ i : Fin 2, A (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)<0 := by
  by_contra hn
  push Not at hn
  exact (not_le_of_gt hA) (Finset.sum_nonneg fun i _ => hn i)

theorem full_test_of_nonexceptional {Ω : Set Plane} {V : Plane → EReal}
    (hΩ : IsOpen Ω) (hV : UpperSemicontinuousOn V Ω)
    (hnon : NonexceptionalTestProperty Ω V) : FullTestProperty Ω V := by
  intro f hf x₀ hx₀ ht
  by_contra hn
  have hΔ : euclideanLaplacian f x₀<0 := lt_of_not_ge hn
  have hgrad : coordinateGradient f x₀=0 := by
    by_contra hg
    exact (not_le_of_gt hΔ) (hnon f hf x₀ hx₀ ht hg)
  obtain ⟨A,r,hA,htr,hr,hball,hdom,hstrict⟩ :=
    exists_strict_quadratic_test hΩ hx₀ hf ht hΔ
  obtain ⟨i,hi⟩ := negative_trace_coordinate htr
  let L : Plane →L[ℝ] ℝ := A (EuclideanSpace.single i 1)
  let q := quadraticAffine (f x₀) (fderiv ℝ f x₀) A x₀
  have hq : Smooth q := smooth_quadraticAffine _ _ _ _
  have hq₀ : q x₀=f x₀ := quadraticAffine_self _ _ _ _
  have hgrad_i : (fderiv ℝ f x₀) (EuclideanSpace.single i 1)=0 := by
    have hh := congrArg (fun v : Plane => v i) hgrad
    simpa only [coordinateGradient_apply, coordPartial, PiLp.zero_apply] using hh
  let H := Metric.sphere x₀ r
  have hH : IsCompact H := isCompact_sphere x₀ r
  have hHball : H⊆Metric.closedBall x₀ r := Metric.sphere_subset_closedBall
  have hW := upperSemicontinuousOn_add_real (hV.mono (hHball.trans hball)) hq.continuous.neg.continuousOn
  have hgap : (⨆ x∈H, V x+((-q x:ℝ):EReal))<0 := by
    apply compact_strict_gap hH hW
    intro x hx
    have hne : x≠x₀ := by
      intro he
      have : r=0 := by simpa [H, he] using (Metric.mem_sphere.mp hx).symm
      linarith
    have hxq := hstrict x (hHball hx) hne
    calc V x+((-q x:ℝ):EReal) < (q x:EReal)+((-q x:ℝ):EReal) :=
          EReal.add_lt_add_right_coe hxq (-q x)
      _ = 0 := by rw [← EReal.coe_add]; simp
  obtain ⟨a,ha,ha0⟩ := EReal.lt_iff_exists_real_btwn.mp hgap
  have ha0' : a<0 := by exact_mod_cast ha0
  let C := ‖L‖*r+1
  have hC : 0<C := by dsimp [C]; positivity
  let t := -a/(2*C)
  have htpos : 0<t := div_pos (neg_pos.mpr ha0') (mul_pos (by norm_num) hC)
  have htC : t*C= -a/2 := by dsimp [t]; field_simp
  let qt := quadraticAffine (f x₀) (fderiv ℝ f x₀-t • L) A x₀
  have hqt : Smooth qt := smooth_quadraticAffine _ _ _ _
  have hqt_eq (x : Plane) : qt x=q x-t*L (x-x₀) := by
    dsimp [qt,q,quadraticAffine]
    simp only [sub_apply,smul_apply,smul_eq_mul]
    ring
  have ht_bound (x : Plane) (hx : x∈Metric.closedBall x₀ r) : t*L (x-x₀)≤ -a/2 := by
    apply le_trans _ htC.le
    apply mul_le_mul_of_nonneg_left _ htpos.le
    have hx' : ‖x-x₀‖≤r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
    calc L (x-x₀) ≤ ‖L (x-x₀)‖ := le_abs_self _
      _ ≤ ‖L‖*‖x-x₀‖ := L.le_opNorm _
      _ ≤ ‖L‖*r := mul_le_mul_of_nonneg_left hx' (norm_nonneg _)
      _ ≤ C := by dsimp [C]; linarith
  have hbdry : ∀ x∈H, V x+((-qt x:ℝ):EReal)<0 := by
    intro x hx
    have hbase : V x+((-q x:ℝ):EReal)<(a:EReal) :=
      (le_iSup₂_of_le x hx le_rfl).trans_lt ha
    have hb := ht_bound x (hHball hx)
    rw [hqt_eq, neg_sub, sub_eq_add_neg, EReal.coe_add]
    rw [add_comm ((t*L (x-x₀):ℝ):EReal), ← add_assoc]
    calc V x+((-q x:ℝ):EReal)+((t*L (x-x₀):ℝ):EReal)
        < (a:EReal)+((t*L (x-x₀):ℝ):EReal) :=
            EReal.add_lt_add_right_coe hbase (t*L (x-x₀))
      _ ≤ (a:EReal)+((-a/2:ℝ):EReal) := add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hb)
      _ < 0 := by rw [← EReal.coe_add]; exact_mod_cast (by linarith : a+-a/2<0)
  have hWball := upperSemicontinuousOn_add_real (hV.mono hball) hqt.continuous.neg.continuousOn
  obtain ⟨xt,hxt,hmax⟩ := hWball.exists_isMaxOn ⟨x₀,Metric.mem_closedBall_self hr.le⟩
    (isCompact_closedBall x₀ r)
  have hzero : V x₀+((-qt x₀:ℝ):EReal)=0 := by
    rw [ht.1, hqt_eq, sub_self, map_zero, mul_zero, sub_zero, hq₀, ← EReal.coe_add]
    simp
  have hmax0 : 0≤V xt+((-qt xt:ℝ):EReal) := by
    rw [← hzero]
    exact hmax (Metric.mem_closedBall_self hr.le)
  have hxtball : xt∈Metric.ball x₀ r := by
    apply Metric.mem_ball.mpr
    apply lt_of_le_of_ne (Metric.mem_closedBall.mp hxt)
    intro he
    exact (not_lt_of_ge hmax0) (hbdry xt (Metric.mem_sphere.mpr he))
  have hfinite : V xt≠⊤ ∧ V xt≠⊥ := by
    constructor
    · exact ne_top_of_le_ne_top (EReal.coe_ne_top _) (hdom xt hxt)
    · intro he
      have hh : (0:EReal)≤⊥ := by simpa only [he, EReal.bot_add] using hmax0
      exact (not_le_of_gt EReal.bot_lt_zero) hh
  have hLpos : 0≤L (xt-x₀) := by
    have hupper := add_le_add (hdom xt hxt) (le_refl ((-qt xt:ℝ):EReal))
    change V xt+((-qt xt:ℝ):EReal)≤(q xt:EReal)+((-qt xt:ℝ):EReal) at hupper
    rw [← EReal.coe_add] at hupper
    have hboth := hmax0.trans hupper
    rw [hqt_eq] at hboth
    have hreal : 0≤q xt+-(q xt-t*L (xt-x₀)) := by
      exact_mod_cast hboth
    have hmul : 0≤t*L (xt-x₀) := by linarith
    exact nonneg_of_mul_nonneg_right hmul htpos
  let ψ := fun x => qt x+(V xt).toReal-qt xt
  have hψ : Smooth ψ := (hqt.add contDiff_const).sub contDiff_const
  have htest : IsUpperTest V ψ xt :=
    upper_test_of_maximum (Metric.ball_subset_interior_closedBall hxtball) hfinite hmax
  have hψgrad : coordinateGradient ψ xt≠0 := by
    intro he
    have hiψ : coordPartial ψ i xt=0 := by
      have hh := congrArg (fun v : Plane => v i) he
      simpa only [coordinateGradient_apply, PiLp.zero_apply] using hh
    have hpartial : coordPartial ψ i xt=L (xt-x₀)-t*A (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
      dsimp only [ψ]
      rw [partial_sub (hqt.add contDiff_const) contDiff_const,
        partial_add hqt contDiff_const]
      simp only [partial_const, add_zero, sub_zero]
      rw [partial_quadraticAffine hA]
      simp only [sub_apply,smul_apply,smul_eq_mul,hgrad_i,zero_sub]
      rw [hA (xt-x₀) (EuclideanSpace.single i 1)]
      dsimp [L]
      ring
    rw [hpartial] at hiψ
    have hprod := mul_neg_of_pos_of_neg htpos hi
    linarith
  have hψΔ : euclideanLaplacian ψ xt=formTrace A := by
    have hψeq : ψ=fun x => qt x+((V xt).toReal-qt xt) := by funext x; dsimp [ψ]; ring
    rw [hψeq, laplacian_add hqt contDiff_const]
    rw [laplacian_const, add_zero]
    exact laplacian_quadraticAffine hA _ _ _ _
  have hh := hnon ψ hψ xt (hball hxt) htest hψgrad
  rw [hψΔ] at hh
  exact (not_le_of_gt htr) hh

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
namespace SharpNodal.Profiles

lemma ereal_add_coe_lt_coe_iff {v : EReal} {a b : ℝ} :
    v+(a:EReal)<(b:EReal) ↔ v<((b-a:ℝ):EReal) := by
  have heq : ((b-a:ℝ):EReal)+(a:EReal)=(b:EReal) := by
    rw [← EReal.coe_add]; congr 1; ring
  constructor
  · intro h
    by_contra hn
    have hh := add_le_add (le_of_not_gt hn) (le_refl (a:EReal))
    rw [heq] at hh
    exact (not_le_of_gt h) hh
  · intro h
    simpa only [heq] using EReal.add_lt_add_right_coe h a

lemma ereal_coe_lt_add_coe_iff {v : EReal} {a b : ℝ} :
    (b:EReal)<v+(a:EReal) ↔ ((b-a:ℝ):EReal)<v := by
  have heq : ((b-a:ℝ):EReal)+(a:EReal)=(b:EReal) := by
    rw [← EReal.coe_add]; congr 1; ring
  constructor
  · intro h
    by_contra hn
    have hh := add_le_add (le_of_not_gt hn) (le_refl (a:EReal))
    rw [heq] at hh
    exact (not_le_of_gt h) hh
  · intro h
    simpa only [heq] using EReal.add_lt_add_right_coe h a

variable {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [OpensMeasurableSpace X]

def weightedMass (μ : Measure X) (S : ℝ) (f : X → ℝ) (E : Set X) : ℝ≥0∞ :=
  ∫⁻ x in E, ENNReal.ofReal (Real.exp (2*S*f x)) ∂μ

omit [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X] in
lemma weightedMass_mono_set (μ : Measure X) (S : ℝ) (f : X → ℝ)
    {E F : Set X} (hEF : E⊆F) : weightedMass μ S f E≤weightedMass μ S f F :=
  lintegral_mono' (Measure.restrict_mono hEF le_rfl) le_rfl

omit [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X] in
lemma weightedMass_upper (μ : Measure X) {S c : ℝ} (hS : 0≤S) (f : X → ℝ)
    {E : Set X} (hf : ∀ x∈E, f x≤c) :
    weightedMass μ S f E≤ENNReal.ofReal (Real.exp (2*S*c))*μ E := by
  have hh := setLIntegral_mono (μ:=μ) (f:=fun x => ENNReal.ofReal (Real.exp (2*S*f x)))
    (g:=fun _ => ENNReal.ofReal (Real.exp (2*S*c))) measurable_const
    (fun x hx => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (hf x hx) (by positivity))))
  simpa only [weightedMass, lintegral_const, Measure.restrict_apply_univ] using hh

omit [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X] in
lemma weightedMass_lower (μ : Measure X) {S c : ℝ} (hS : 0≤S) (f : X → ℝ)
    {E : Set X} (hE : MeasurableSet E) (hf : ∀ x∈E, c≤f x) :
    ENNReal.ofReal (Real.exp (2*S*c))*μ E≤weightedMass μ S f E := by
  have hh := setLIntegral_mono' (μ:=μ) hE (f:=fun _ => ENNReal.ofReal (Real.exp (2*S*c)))
    (g:=fun x => ENNReal.ofReal (Real.exp (2*S*f x))) (fun x hx =>
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hf x hx) (by positivity))))
  simpa only [weightedMass, lintegral_const, Measure.restrict_apply_univ] using hh

omit [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X] in
lemma weightedMass_biUnion_le (μ : Measure X) (S : ℝ) (f : X → ℝ)
    {I : Type*} (t : Finset I) (E : I → Set X) :
    weightedMass μ S f (⋃ i∈t, E i)≤∑ i∈t, weightedMass μ S f (E i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [weightedMass]
  | @insert i t hi ih =>
    simpa only [weightedMass, Finset.mem_insert, iUnion_iUnion_eq_or_left, Finset.sum_insert hi]
      using (lintegral_union_le (μ:=μ) (fun x => ENNReal.ofReal (Real.exp (2*S*f x)))
        (E i) (⋃ j∈t, E j)).trans (add_le_add le_rfl ih)

omit [OpensMeasurableSpace X] in
lemma basis_rates_mono {μ : ℕ → Measure X} {S : ℕ → ℝ}
    {ell : countableBasis X → EReal} (hS : ∀ j, 0<S j)
    (hlim : ∀ i : countableBasis X,
      Tendsto (fun j => logRate (S j) (μ j i.val)) atTop (𝓝 (ell i)))
    {i k : countableBasis X} (hik : i.val⊆k.val) : ell i≤ell k :=
  le_of_tendsto_of_tendsto (hlim i) (hlim k)
    (Eventually.of_forall fun j => logRate_mono (hS j) (measure_mono hik))

omit [OpensMeasurableSpace X] in

theorem weighted_compact_profile_upper {μ : ℕ → Measure X} {S : ℕ → ℝ}
    {ell : countableBasis X → EReal} {Ω : Set X} (hΩ : IsOpen Ω)
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop)
    (hlim : ∀ i : countableBasis X,
      Tendsto (fun j => logRate (S j) (μ j i.val)) atTop (𝓝 (ell i)))
    {f : X → ℝ} (hf : ContinuousOn f Ω) {F : Set X} (hF : IsCompact F) (hFΩ : F⊆Ω) :
    limsup (fun j => logRate (S j) (weightedMass (μ j) (S j) f F)) atTop≤
      ⨆ x∈F, basisProfile ell x+(f x:EReal) := by
  classical
  by_contra hn
  obtain ⟨b,hVb,hbL⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
  obtain ⟨a,hVa,hab⟩ := EReal.lt_iff_exists_real_btwn.mp hVb
  have hab' : a<b := by exact_mod_cast hab
  let I := {p : countableBasis X × ℝ // ell p.1<((a-p.2:ℝ):EReal) ∧
    ∀ y∈p.1.val, f y≤p.2}
  let U : I → Set X := fun p => p.val.1.val
  have hcover : F⊆⋃ p, U p := by
    intro x hx
    have hxa : basisProfile ell x+(f x:EReal)<(a:EReal) :=
      (le_iSup₂_of_le x hx le_rfl).trans_lt hVa
    obtain ⟨z,hVz,hzf⟩ := EReal.lt_iff_exists_real_btwn.mp (ereal_add_coe_lt_coe_iff.mp hxa)
    have hfz : f x<a-z := by
      have : z<a-f x := by exact_mod_cast hzf
      linarith
    obtain ⟨i,hxi,hiz⟩ := (basisProfile_lt_iff ell x z).mp hVz
    have hevent : ∀ᶠ y in 𝓝 x, y∈i.val ∧ f y<a-z :=
      Filter.Eventually.and ((isOpen_of_mem_countableBasis i.property).mem_nhds hxi)
        ((hf.continuousAt (hΩ.mem_nhds (hFΩ hx))).eventually (gt_mem_nhds hfz))
    obtain ⟨J,hJ,hxJ,hsub⟩ := (isBasis_countableBasis X).mem_nhds_iff.mp hevent
    let k : countableBasis X := ⟨J,hJ⟩
    have hkz : ell k<((a-(a-z):ℝ):EReal) := by
      rw [show a-(a-z)=z by ring]
      exact (basis_rates_mono hSpos hlim (fun y hy => (hsub hy).1)).trans_lt hiz
    let p : I := ⟨(k,a-z),hkz,fun y hy => (hsub hy).2.le⟩
    exact mem_iUnion.mpr ⟨p,hxJ⟩
  obtain ⟨t,ht⟩ := hF.elim_finite_subcover U
    (fun p => isOpen_of_mem_countableBasis p.val.1.property) hcover
  have hterms : ∀ᶠ j in atTop, ∀ p∈t,
      weightedMass (μ j) (S j) f (U p)≤ENNReal.ofReal (Real.exp (2*S j*a)) := by
    apply (eventually_all_finset t).mpr
    intro p hp
    filter_upwards [(hlim p.val.1).eventually (gt_mem_nhds p.property.1)] with j hj
    have hr := (weightedMass_upper (μ j) (hSpos j).le f p.property.2).trans
      (mul_le_mul' le_rfl ((logRate_lt_iff (hSpos j) _).mp hj).le)
    convert! hr using 1
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  have hc : 0<(t.card:ℝ)+1 := by positivity
  have hgap := exponential_gap hS hab' hc
  have hbound : ∀ᶠ j in atTop,
      logRate (S j) (weightedMass (μ j) (S j) f F)≤(b:EReal) := by
    filter_upwards [hterms,hgap] with j hj hg
    apply (logRate_le_iff (hSpos j) _).mpr
    apply ((weightedMass_mono_set _ _ _ ht).trans (weightedMass_biUnion_le _ _ _ t U)).trans
    calc (∑ p∈t, weightedMass (μ j) (S j) f (U p))
        ≤ ∑ _p∈t, ENNReal.ofReal (Real.exp (2*S j*a)) := Finset.sum_le_sum fun p hp => hj p hp
      _ = (t.card:ℝ≥0∞)*ENNReal.ofReal (Real.exp (2*S j*a)) := by simp
      _ ≤ ENNReal.ofReal ((t.card:ℝ)+1)*ENNReal.ofReal (Real.exp (2*S j*a)) := by
        gcongr
        exact_mod_cast (le_add_of_nonneg_right (show (0:ℝ)≤1 by norm_num) : (t.card:ℝ)≤(t.card:ℝ)+1)
      _ = ENNReal.ofReal (((t.card:ℝ)+1)*Real.exp (2*S j*a)) := (ENNReal.ofReal_mul hc.le).symm
      _ ≤ ENNReal.ofReal (Real.exp (2*S j*b)) := ENNReal.ofReal_le_ofReal hg.le
  exact (not_le_of_gt hbL) (limsup_le_of_le (by isBoundedDefault) hbound)

theorem weighted_open_profile_lower {μ : ℕ → Measure X} {S : ℕ → ℝ}
    {ell : countableBasis X → EReal} {Ω : Set X} (hΩ : IsOpen Ω)
    (hSpos : ∀ j, 0<S j)
    (hlim : ∀ i : countableBasis X,
      Tendsto (fun j => logRate (S j) (μ j i.val)) atTop (𝓝 (ell i)))
    {f : X → ℝ} (hf : ContinuousOn f Ω) {G : Set X} (hG : IsOpen G) (hGΩ : G⊆Ω) :
    (⨆ x∈G, basisProfile ell x+(f x:EReal))≤
      liminf (fun j => logRate (S j) (weightedMass (μ j) (S j) f G)) atTop := by
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  by_contra hn
  obtain ⟨b,hLb,hbV⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
  obtain ⟨z,hbz,hzV⟩ := EReal.lt_iff_exists_real_btwn.mp (ereal_coe_lt_add_coe_iff.mp hbV)
  have hcz : b-z<f x := by
    have : b-f x<z := by exact_mod_cast hbz
    linarith
  have hevent : ∀ᶠ y in 𝓝 x, y∈G ∧ b-z<f y :=
    Filter.Eventually.and (hG.mem_nhds hx) ((hf.continuousAt (hΩ.mem_nhds (hGΩ hx))).eventually (lt_mem_nhds hcz))
  obtain ⟨J,hJ,hxJ,hsub⟩ := (isBasis_countableBasis X).mem_nhds_iff.mp hevent
  let i : countableBasis X := ⟨J,hJ⟩
  have hzi : (z:EReal)<ell i := hzV.trans_le (basisProfile_le ell i hxJ)
  have hbound : ∀ᶠ j in atTop, (b:EReal)≤logRate (S j) (weightedMass (μ j) (S j) f G) := by
    filter_upwards [(hlim i).eventually (lt_mem_nhds hzi)] with j hj
    apply (le_logRate_iff (hSpos j) _).mpr
    have hl := weightedMass_lower (μ j) (hSpos j).le f
      (isOpen_of_mem_countableBasis hJ).measurableSet (fun y hy => (hsub hy).2.le)
    have hm := (mul_le_mul' le_rfl ((lt_logRate_iff (hSpos j) _).mp hj).le).trans hl
    have hh := hm.trans (weightedMass_mono_set _ _ _ (fun y hy => (hsub hy).1))
    convert! hh using 1
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  exact (not_le_of_gt hLb) (le_liminf_of_le (by isBoundedDefault) hbound)

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
namespace SharpNodal.Profiles
open Carleman

def tiltedDensity (B : Plane) (U : Plane → ℝ) (c : ℝ) (x : Plane) : ℝ≥0∞ :=
  ENNReal.ofReal (c*(Real.exp (-inner ℝ B x)*U x)^2)

def tiltedMeasure (Ω : Set Plane) (B : Plane) (U : Plane → ℝ) (c : ℝ) : Measure Plane :=
  (volume.restrict Ω).withDensity (tiltedDensity B U c)

lemma continuousOn_tiltedDensity {Ω : Set Plane} {U : Plane → ℝ}
    (hU : ContinuousOn U Ω) (B : Plane) (c : ℝ) :
    ContinuousOn (tiltedDensity B U c) Ω := by
  apply ENNReal.continuous_ofReal.comp_continuousOn
  exact continuousOn_const.mul (((Real.continuous_exp.comp (innerSL ℝ B).continuous.neg).continuousOn.mul hU).pow 2)

lemma tiltedDensity_weight (S : ℝ) (B : Plane) (U f : Plane → ℝ) (c : ℝ) (x : Plane) :
    tiltedDensity B U c x*ENNReal.ofReal (Real.exp (2*S*f x)) =
      ENNReal.ofReal (c*(Real.exp (tiltedWeight B S (fun y => -f y) x)*U x)^2) := by
  unfold tiltedDensity
  rw [← ENNReal.ofReal_mul' (Real.exp_pos _).le]
  congr 1
  unfold tiltedWeight
  rw [mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  simp only [Nat.cast_ofNat]
  calc c*(Real.exp (2*(-inner ℝ B x))*U x^2)*Real.exp (2*S*f x)
      = c*(Real.exp (2*(-inner ℝ B x))*Real.exp (2*S*f x))*U x^2 := by ring
    _ = _ := by
      rw [← Real.exp_add, show 2*(-inner ℝ B x)+2*S*f x=2*(-inner ℝ B x-S*(-f x)) by ring]
      ring

lemma weightedMass_tiltedMeasure {Ω E : Set Plane}
    (hE : MeasurableSet E) (hEΩ : E⊆Ω) {U : Plane → ℝ} (hU : ContinuousOn U Ω)
    (S : ℝ) (B : Plane) (c : ℝ) (f : Plane → ℝ) :
    weightedMass (tiltedMeasure Ω B U c) S f E=tiltedMass S B U c f E := by
  unfold weightedMass tiltedMeasure
  rw [restrict_withDensity hE, Measure.restrict_restrict_of_subset hEΩ]
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _
    ((continuousOn_tiltedDensity hU B c).mono hEΩ |>.aemeasurable hE)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) ]
  exact lintegral_congr fun x => tiltedDensity_weight S B U f c x

theorem extract_tilted_profile {Ω : Set Plane} (hΩ : IsOpen Ω)
    (S : ℕ → ℝ) (B : ℕ → Plane) (U : ℕ → Plane → ℝ) (c : ℕ → ℝ)
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop)
    (hU : ∀ j, ContinuousOn (U j) Ω)
    (hnorm : ∀ j, tiltedMass (S j) (B j) (U j) (c j) 0 Ω≤1) :
    ∃ (V : Plane → EReal) (φ : ℕ → ℕ), StrictMono φ ∧ UpperSemicontinuous V ∧
      (∀ x, V x≤0) ∧
      WeightedProfileBounds Ω (S∘φ) (B∘φ) (U∘φ) (c∘φ) V := by
  let μ := fun j => tiltedMeasure Ω (B j) (U j) (c j)
  obtain ⟨ell,φ,hφ,hlim⟩ := extract_basis_rates μ S
  refine ⟨basisProfile ell,φ,hφ,upperSemicontinuous_basisProfile ell,?_,?_⟩
  · apply basisProfile_nonpos
    apply basis_rates_nonpos hSpos _ hlim
    intro j
    have heq : μ j univ=tiltedMass (S j) (B j) (U j) (c j) 0 Ω := by
      simp only [μ,tiltedMeasure,withDensity_apply _ MeasurableSet.univ,
        Measure.restrict_univ]
      apply lintegral_congr
      intro x
      simp [tiltedDensity,tiltedWeight]
    rw [heq]
    exact hnorm j
  · constructor
    · intro f hf F hF hFΩ
      have heq (j : ℕ) := weightedMass_tiltedMeasure hF.measurableSet hFΩ
        (hU (φ j)) (S (φ j)) (B (φ j)) (c (φ j)) f
      simpa only [Function.comp_apply,← heq] using
        weighted_compact_profile_upper hΩ (fun j => hSpos (φ j))
          (hS.comp hφ.tendsto_atTop) hlim hf hF hFΩ
    · intro f hf G hG hGΩ
      have heq (j : ℕ) := weightedMass_tiltedMeasure hG.measurableSet hGΩ
        (hU (φ j)) (S (φ j)) (B (φ j)) (c (φ j)) f
      simpa only [Function.comp_apply,← heq] using
        weighted_open_profile_lower hΩ (fun j => hSpos (φ j)) hlim hf hG hGΩ
end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

def ShiftedTestProperty (Ω : Set Plane) (V : Plane → EReal) (b : Plane) (d : ℝ) : Prop :=
  ∀ (f : Plane → ℝ), Smooth f → ∀ x₀∈Ω, IsUpperTest V f x₀ →
    b+d • coordinateGradient f x₀≠0 → 0≤euclideanLaplacian f x₀

theorem shifted_test_of_profile
    {Ω : Set Plane} {p U : ℕ → Plane → ℝ} {V : Plane → EReal}
    {B : ℕ → Plane} {S D K e c : ℕ → ℝ} {b : Plane} {d Cp : ℝ}
    (hΩ : IsOpen Ω) (hp : ∀ j, ContDiffOn ℝ ∞ (p j) Ω)
    (hU : ∀ j, ContDiffOn ℝ ∞ (U j) Ω)
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop)
    (hc : ∀ j, 0<c j) (hDdef : ∀ j, D j=S j+‖B j‖)
    (hb : Tendsto (fun j => (D j)⁻¹ • B j) atTop (𝓝 b))
    (hd : Tendsto (fun j => S j/D j) atTop (𝓝 d))
    (hK : Tendsto (fun j => K j/D j) atTop (𝓝 0))
    (hpbound : ∀ j x, x∈Ω → |p j x|≤Cp)
    (he : Tendsto e atTop (𝓝 0))
    (hpgrad : ∀ j i x, x∈Ω →
      |(K j)^2*coordPartial (p j) i x/(S j*D j)|≤e j)
    (hPDE : ∀ j x, x∈Ω → euclideanLaplacian (U j) x+(K j)^2*p j x*U j x=0)
    (hV : UpperSemicontinuousOn V Ω) (hprofile : WeightedProfileBounds Ω S B U c V) :
    ShiftedTestProperty Ω V b d := by
  intro f hf x₀ hx₀ ht ha
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp
    (Filter.Eventually.and (hΩ.mem_nhds hx₀) ht.2)
  have hball : Metric.ball x₀ r⊆Ω := fun x hx => (hsub hx).1
  have hs := laplacian_nonneg_of_strict_contact hΩ hx₀ hball
    (hf.add (smooth_contactQuartic x₀)).contDiffOn hp hU hr hSpos hS hc hDdef
    hb hd hK (fun j x hx => hpbound j x (hball hx)) he
    (fun j i x hx => hpgrad j i x (hball hx))
    (fun j x hx => hPDE j x (hball hx))
    (by simpa only [strictify_gradient hf] using ha) hV hprofile
    (by simpa only [EReal.coe_neg] using strictify_contact (x₀:=x₀) ht.1)
    (fun x hx hne => by simpa only [EReal.coe_neg] using strictify_strict (hsub hx).2 hne)
  simpa only [strictify_laplacian hf] using hs

lemma gradient_sub_linear (B : Plane) {f : Plane → ℝ} (hf : Smooth f) (x : Plane) :
    coordinateGradient (fun y => f y-inner ℝ B y) x=coordinateGradient f x-B := by
  have hL : Smooth (fun y : Plane => inner ℝ B y) := (innerSL ℝ B).contDiff
  ext i
  simp only [coordinateGradient_apply, PiLp.sub_apply, partial_sub hf hL,partial_linear]

lemma laplacian_sub_linear (B : Plane) {f : Plane → ℝ} (hf : Smooth f) (x : Plane) :
    euclideanLaplacian (fun y => f y-inner ℝ B y) x=euclideanLaplacian f x := by
  have hL : Smooth (fun y : Plane => inner ℝ B y) := (innerSL ℝ B).contDiff
  unfold euclideanLaplacian
  apply Finset.sum_congr rfl
  intro i _
  rw [show coordPartial (fun y => f y-inner ℝ B y) i =fun y => coordPartial f i y-B i by
    ext y; rw [partial_sub hf hL,partial_linear]]
  rw [partial_sub (smooth_partial hf i) contDiff_const,partial_const,sub_zero]

lemma upperTest_sub_real {V : Plane → EReal} {f L : Plane → ℝ} {x : Plane}
    (ht : IsUpperTest (fun y => V y+(L y:EReal)) f x) :
    IsUpperTest V (fun y => f y-L y) x := by
  have hcancel (y : Plane) : (V y+(L y:EReal))+((-L y:ℝ):EReal)=V y := by
    rw [add_assoc,← EReal.coe_add]; simp
  constructor
  · have ht₀ : V x+(L x:EReal)=(f x:EReal) := ht.1
    rw [← hcancel x,ht₀,← EReal.coe_add]
    rfl
  · filter_upwards [ht.2] with y hy
    have hh := add_le_add hy (le_refl ((-L y:ℝ):EReal))
    simpa only [hcancel,← EReal.coe_add,sub_eq_add_neg] using hh

lemma upperTest_add_real {V : Plane → EReal} {f L : Plane → ℝ} {x : Plane}
    (ht : IsUpperTest V f x) :
    IsUpperTest (fun y => V y+(L y:EReal)) (fun y => f y+L y) x := by
  constructor
  · change V x+(L x:EReal)=((f x+L x:ℝ):EReal)
    rw [ht.1,EReal.coe_add]
  · filter_upwards [ht.2] with y hy
    rw [EReal.coe_add]
    exact add_le_add hy le_rfl

theorem full_test_of_shifted {Ω : Set Plane} {V : Plane → EReal} {b : Plane} {d : ℝ}
    (hΩ : IsOpen Ω) (hV : UpperSemicontinuousOn V Ω) (hd : 0≤d)
    (hnorm : d+‖b‖=1) (hshift : ShiftedTestProperty Ω V b d) :
    FullTestProperty Ω V := by
  rcases hd.eq_or_lt with hd | hd
  · have hb : b≠0 := by intro he; simp [← hd,he] at hnorm
    intro f hf x hx ht
    apply hshift f hf x hx ht
    simpa only [← hd,zero_smul,add_zero] using hb
  · let B : Plane := d⁻¹ • b
    let W : Plane → EReal := fun x => V x+(inner ℝ B x:EReal)
    have hW : UpperSemicontinuousOn W Ω :=
      upperSemicontinuousOn_add_real hV (innerSL ℝ B).continuous.continuousOn
    have hnon : NonexceptionalTestProperty Ω W := by
      intro f hf x hx ht hgrad
      have hs := hshift (fun y => f y-inner ℝ B y) (hf.sub (innerSL ℝ B).contDiff)
        x hx (upperTest_sub_real ht) ?_
      · simpa only [laplacian_sub_linear B hf] using hs
      · rw [gradient_sub_linear B hf,smul_sub,show d • B=b by
          dsimp [B]; rw [smul_smul,mul_inv_cancel₀ hd.ne',one_smul]]
        rw [show b+(d • coordinateGradient f x-b)=d • coordinateGradient f x by abel]
        exact smul_ne_zero hd.ne' hgrad
    have hfull := full_test_of_nonexceptional hΩ hW hnon
    intro f hf x hx ht
    have hs := hfull (fun y => f y+inner ℝ B y) (hf.add (innerSL ℝ B).contDiff)
      x hx (upperTest_add_real ht)
    have heq : (fun y => f y+inner ℝ B y)=(fun y => f y-inner ℝ (-B) y) := by
      ext y; simp
    rw [heq,laplacian_sub_linear (-B) hf] at hs
    exact hs
end SharpNodal.Profiles

end
end
end
end
end

end OAI
