import OAI.Analysis.AllenCahn.PositiveJets
import OAI.Analysis.AllenCahn.JetCompactness

namespace OAI

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped ContDiff
open Filter Topology
open DeGiorgiCompactness (JetSpace CoherentJets)

lemma coherentJets_identify {n : ℕ} {g : JetSpace n} (hg : CoherentJets g)
    (l : List (Fin n)) : (g l : Space n → ℝ) = coordinateJet (g [] : Space n → ℝ) l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    funext x
    rw [← (hg l).2 i x, ih]
    rfl

theorem all_jet_subsequence {n : ℕ} {ι : Type*} [Countable ι]
    {f : ℕ → ι → Space n → ℝ} (hf : ∀ j i, ContDiff ℝ ∞ (f j i))
    (hb : ∀ i l R, 0 < R → ∃ M : ℝ, 0 ≤ M ∧ ∀ j x, ‖x‖ ≤ R →
      |coordinateJet (f j i) l x| ≤ M) :
    ∃ (a : ℕ → ℕ) (g : ι → Space n → ℝ), StrictMono a ∧
      (∀ i, ContDiff ℝ ∞ (g i)) ∧ ∀ i l,
        TendstoLocallyUniformly (fun j => coordinateJet (f (a j) i) l)
          (coordinateJet (g i) l) atTop := by
  let F (j : ℕ) (z : ι × List (Fin n)) := coordinateJet (f j z.1) z.2
  have hF (j z) : Differentiable ℝ (F j z) :=
    (coordinateJet_smooth (hf j z.1) z.2).differentiable (by simp)
  have hB (z : ι × List (Fin n)) (R : ℝ) (hR : 0<R) : ∃ M : ℝ≥0,
      ∀ j x, ‖x‖ ≤ R → |F j z x| ≤ M ∧ ‖fderiv ℝ (F j z) x‖ ≤ M := by
    obtain ⟨C,hC,hCb⟩ := hb z.1 z.2 R hR
    choose N hN hNb using fun i : Fin n => hb z.1 (i::z.2) R hR
    let M := C+‖DeGiorgiCompactness.coordinateDual n‖*(∑ i, N i)
    have hNS : 0 ≤ ∑ i, N i := Finset.sum_nonneg (fun i _ => hN i)
    have hM : 0 ≤ M := by dsimp [M]; positivity
    refine ⟨⟨M,hM⟩,fun j x hx => ⟨?_, ?_⟩⟩
    · exact (hCb j x hx).trans (le_add_of_nonneg_right (mul_nonneg (norm_nonneg (DeGiorgiCompactness.coordinateDual n)) hNS))
    · have H := DeGiorgiCompactness.fderiv_norm_le_coord_bound (F j z) x hNS (fun i =>
        (hNb i j x hx).trans (Finset.single_le_sum (fun a _ => hN a) (Finset.mem_univ i)))
      exact H.trans (le_add_of_nonneg_left hC)
  obtain ⟨a,G,ha,hlim⟩ := DeGiorgiCompactness.countable_local_compactness hF hB
  let J (i : ι) : JetSpace n := fun l => G (i,l)
  have hcoh (i : ι) : CoherentJets (J i) := by
    intro l
    have hloc (l) : TendstoLocallyUniformly (fun j => coordinateJet (f (a j) i) l) (J i l) atTop :=
      hlim (i,l)
    have H := DeGiorgiCompactness.first_jet_limit
      (fun j => (coordinateJet_smooth (hf (a j) i) l).differentiable (by simp))
      (J i l) (fun k => J i (k::l)) (hloc l) (fun k => hloc (k::l))
    exact ⟨H.1.differentiable (by norm_num),H.2.1⟩
  refine ⟨a,fun i => J i [],ha,fun i => DeGiorgiCompactness.coherentJets_smooth (hcoh i) [], ?_⟩
  intro i l
  rw [← coherentJets_identify (hcoh i) l]
  exact hlim (i,l)

def smallDefectEntry {n : ℕ} (v : Space n → ℝ)
    (i : Option (Option (Fin n × Fin n))) : Space n → ℝ :=
  match i with
  | none => inverseProfile v
  | some none => diffuseDefect v
  | some (some (a,b)) => inverseHessian v a b

def smallDefectScale {n : ℕ} (v : Space n → ℝ)
    (i : Option (Option (Fin n × Fin n))) : ℝ :=
  match i with
  | none => 1
  | some none => diffuseDefect v 0
  | some (some _) => defectRoot v 0

lemma smallDefectEntry_smooth {n : ℕ} {v : Space n → ℝ}
    (hv : v ∈ positiveDefectClass n) (i : Option (Option (Fin n × Fin n))) :
    ContDiff ℝ ∞ (smallDefectEntry v i) := by
  rcases i with _ | (_ | ⟨a,b⟩)
  · exact inverseProfile_smooth hv.1 hv.2.1
  · exact diffuseDefect_smooth hv.1 hv.2.1
  · exact inverseHessian_smooth hv.1 hv.2.1 a b

lemma smallDefectScale_pos {n : ℕ} {v : Space n → ℝ}
    (hv : v ∈ positiveDefectClass n) (i : Option (Option (Fin n × Fin n))) :
    0 < smallDefectScale v i := by
  rcases i with _ | (_ | ⟨a,b⟩)
  · exact zero_lt_one
  · exact hv.2.2.2 0
  · exact defectRoot_pos v 0

lemma defectRoot_ball_comparison {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : AllenCahn v)
    (hp : ∀ x, 0 < diffuseDefect v x) {R : ℝ} (hR : 0 ≤ R) {x : Space n} (hx : ‖x‖ ≤ R) :
    defectRoot v x ≤ Real.exp (relativeDefectConstant n * R) * defectRoot v 0 := by
  let K := Real.exp (relativeDefectConstant n * R)
  have hK : 1 ≤ K := Real.one_le_exp (mul_nonneg (relativeDefectConstant_pos n).le hR)
  have H : diffuseDefect v x ≤ K * diffuseDefect v 0 := by
    apply (diffuseDefect_exp_comparison_crude hv hi hAC hp 0 x).trans
    apply mul_le_mul_of_nonneg_right _ (hp 0).le
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by simpa using hx) (relativeDefectConstant_pos n).le
  have H' : diffuseDefect v x ≤ K ^ 2 * diffuseDefect v 0 :=
    H.trans (mul_le_mul_of_nonneg_right (by nlinarith : K ≤ K ^ 2) (hp 0).le)
  have hsx := defectRoot_sq (hp x)
  have hs0 := defectRoot_sq (hp 0)
  have hpos := defectRoot_pos v x
  have hpos0 := defectRoot_pos v 0
  rw [← hsx, ← hs0, ← mul_pow] at H'
  have hk0 : 0 ≤ K * defectRoot v 0 := mul_nonneg (by linarith) hpos0.le
  exact (sq_le_sq₀ hpos.le hk0).mp H'

lemma inverseProfile_zero {n : ℕ} {v : Space n → ℝ} (h0 : v 0=0) : inverseProfile v 0=0 := by
  simp [inverseProfile,h0]

lemma inverseProfile_local_bound {n : ℕ} {v : Space n → ℝ}
    (hv : v ∈ positiveDefectClass n) (h0 : v 0=0) (x : Space n) : |inverseProfile v x| ≤ ‖x‖ := by
  have hg (y) : ‖fderiv ℝ (inverseProfile v) y‖ ≤ 1 := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      inverseProfile_gradient_bound (smooth_C2 hv.1) hv.2.1 hv.2.2.1 y
  have H := (convex_univ : Convex ℝ (Set.univ : Set (Space n))).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => (inverseProfile_smooth hv.1 hv.2.1).differentiable (by simp) y)
    (fun y _ => hg y) (Set.mem_univ x) (Set.mem_univ 0)
  simpa [inverseProfile_zero h0, Real.norm_eq_abs] using H

lemma smallDefect_normalized_local_bounds (n : ℕ)
    (i : Option (Option (Fin n × Fin n))) (l : List (Fin n)) (R : ℝ) (hR : 0<R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ v ∈ positiveDefectClass n, v 0=0 → ∀ x, ‖x‖ ≤ R →
      |coordinateJet (fun y => (smallDefectScale v i)⁻¹*smallDefectEntry v i y) l x| ≤ M := by
  have norm_control {w f : (Space n → ℝ) → Space n → ℝ}
      (hf : ∀ v ∈ positiveDefectClass n, ContDiff ℝ ∞ (f v))
      (hc : ∀ v ∈ positiveDefectClass n, 0 < w v 0)
      (hJ : JetControl (positiveDefectClass n) w f l.length)
      (hb : ∀ v ∈ positiveDefectClass n, ∀ x, ‖x‖ ≤ R →
        w v x ≤ Real.exp (relativeDefectConstant n*R)*w v 0) :
      ∃ M : ℝ, 0 ≤ M ∧ ∀ v ∈ positiveDefectClass n, ∀ x, ‖x‖ ≤ R →
        |coordinateJet (fun y => (w v 0)⁻¹*f v y) l x| ≤ M := by
    obtain ⟨C,hC,hCb⟩ := hJ l le_rfl
    refine ⟨C*Real.exp (relativeDefectConstant n*R),by positivity,fun v hv x hx => ?_⟩
    rw [coordinateJet_const_mul (hf v hv),abs_mul,abs_of_pos (inv_pos.mpr (hc v hv))]
    have H := (hCb v hv x).trans (mul_le_mul_of_nonneg_left (hb v hv x hx) hC)
    have H' := mul_le_mul_of_nonneg_left H (inv_pos.mpr (hc v hv)).le
    calc _ ≤ (w v 0)⁻¹*(C*(Real.exp (relativeDefectConstant n*R)*w v 0)) := H'
      _ = C*Real.exp (relativeDefectConstant n*R) := by field_simp [(hc v hv).ne']
  rcases i with _ | (_ | ⟨a,b⟩)
  · cases l with
    | nil =>
      refine ⟨R,hR.le, ?_⟩
      intro v hv h0 x hx
      simpa only [smallDefectScale,smallDefectEntry,coordinateJet,inv_one,one_mul] using
        (inverseProfile_local_bound hv h0 x).trans hx
    | cons i l =>
      obtain ⟨C,hC,hCb⟩ := (positiveAC_all_jets n l.length).2.1 i l le_rfl
      refine ⟨C,hC,fun v hv _ x _ => ?_⟩
      simpa only [smallDefectScale,smallDefectEntry,inv_one,one_mul,
        coordinateJet_coordDeriv (inverseProfile_smooth hv.1 hv.2.1),coordinateJet,mul_one] using hCb v hv x
  · obtain ⟨M,hM,hb⟩ := norm_control
      (fun v hv => diffuseDefect_smooth hv.1 hv.2.1) (fun v hv => hv.2.2.2 0)
      (positiveAC_all_jets n l.length).2.2.1 (by
        intro v hv x hx
        apply (diffuseDefect_exp_comparison_crude hv.1 hv.2.1 hv.2.2.1 hv.2.2.2 0 x).trans
        apply mul_le_mul_of_nonneg_right _ (hv.2.2.2 0).le
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (by simpa using hx) (relativeDefectConstant_pos n).le)
    exact ⟨M,hM,fun v hv _ => hb v hv⟩
  · obtain ⟨M,hM,hb⟩ := norm_control
      (fun v hv => inverseHessian_smooth hv.1 hv.2.1 a b) (fun v _ => defectRoot_pos v 0)
      ((positiveAC_all_jets n l.length).2.2.2 a b) (fun v hv x hx =>
        defectRoot_ball_comparison hv.1 hv.2.1 hv.2.2.1 hv.2.2.2 hR.le hx)
    exact ⟨M,hM,fun v hv _ => hb v hv⟩

theorem smallDefect_smooth_compactness {n : ℕ} {v : ℕ → Space n → ℝ}
    (hv : ∀ j, v j ∈ positiveDefectClass n) (h0 : ∀ j, v j 0=0) :
    ∃ (a : ℕ → ℕ) (g : Option (Option (Fin n × Fin n)) → Space n → ℝ), StrictMono a ∧
      (∀ i, ContDiff ℝ ∞ (g i)) ∧ ∀ i l,
        TendstoLocallyUniformly (fun j => coordinateJet (fun x =>
          (smallDefectScale (v (a j)) i)⁻¹*smallDefectEntry (v (a j)) i x) l)
          (coordinateJet (g i) l) atTop := by
  apply all_jet_subsequence (f := fun j i x => (smallDefectScale (v j) i)⁻¹*smallDefectEntry (v j) i x)
  · intro j i
    exact contDiff_const.mul (smallDefectEntry_smooth (hv j) i)
  · intro i l R hR
    obtain ⟨M,hM,hb⟩ := smallDefect_normalized_local_bounds n i l R hR
    exact ⟨M,hM,fun j => hb (v j) (hv j) (h0 j)⟩

end DeGiorgi
end

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped ContDiff
open Filter Topology

abbrev SmallDefectIndex (n : ℕ) := Option (Option (Fin n × Fin n))

def normalizedSmallJet {n : ℕ} (v : Space n → ℝ) (i : SmallDefectIndex n)
    (l : List (Fin n)) (x : Space n) : ℝ :=
  (smallDefectScale v i)⁻¹*coordinateJet (smallDefectEntry v i) l x

def SmallDefectConverges {n : ℕ} (v : ℕ → Space n → ℝ)
    (g : SmallDefectIndex n → Space n → ℝ) : Prop :=
  (∀ i, ContDiff ℝ ∞ (g i)) ∧ ∀ i l,
    TendstoLocallyUniformly (fun j => normalizedSmallJet (v j) i l) (coordinateJet (g i) l) atTop

lemma SmallDefectConverges.at {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (i : SmallDefectIndex n) (l : List (Fin n)) (x : Space n) :
    Tendsto (fun j => normalizedSmallJet (v j) i l x) atTop (𝓝 (coordinateJet (g i) l x)) :=
  (hg.2 i l).tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ x)

lemma smallDefect_compactness {n : ℕ} {v : ℕ → Space n → ℝ}
    (hv : ∀ j, v j ∈ positiveDefectClass n) (h0 : ∀ j, v j 0=0) :
    ∃ (a : ℕ → ℕ) (g : SmallDefectIndex n → Space n → ℝ), StrictMono a ∧
      SmallDefectConverges (fun j => v (a j)) g := by
  obtain ⟨a,g,ha,hg,hl⟩ := smallDefect_smooth_compactness hv h0
  refine ⟨a,g,ha,hg,fun i l => ?_⟩
  have he : (fun j => normalizedSmallJet (v (a j)) i l) = fun j => coordinateJet
      (fun x => (smallDefectScale (v (a j)) i)⁻¹*smallDefectEntry (v (a j)) i x) l := by
    funext j x
    rw [coordinateJet_const_mul (smallDefectEntry_smooth (hv (a j)) i)]
    rfl
  rw [he]
  exact hl i l

lemma smallDefect_root_tendsto {n : ℕ} {v : ℕ → Space n → ℝ}
    (hv : ∀ j, v j ∈ positiveDefectClass n)
    (he : Tendsto (fun j => diffuseDefect (v j) 0) atTop (𝓝 0)) :
    Tendsto (fun j => defectRoot (v j) 0) atTop (𝓝 0) := by
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp he
  have hfun : (fun j => defectRoot (v j) 0) = fun j => Real.sqrt (diffuseDefect (v j) 0) :=
    funext (fun j => defectRoot_eq_sqrt ((hv j).2.2.2 0))
  rw [hfun]
  simpa only [Real.sqrt_zero, Function.comp_def] using hh

lemma SmallDefectConverges.tensor_vanishes {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (hv : ∀ j, v j ∈ positiveDefectClass n)
    (he : Tendsto (fun j => diffuseDefect (v j) 0) atTop (𝓝 0))
    (a b : Fin n) (l : List (Fin n)) (x : Space n) :
    Tendsto (fun j => coordinateJet (inverseHessian (v j) a b) l x) atTop (𝓝 0) := by
  have HH := (smallDefect_root_tendsto hv he).mul (hg.at (some (some (a,b))) l x)
  have heq : (fun j => defectRoot (v j) 0*normalizedSmallJet (v j) (some (some (a,b))) l x) =
      fun j => coordinateJet (inverseHessian (v j) a b) l x := by
    funext j
    simp only [normalizedSmallJet,smallDefectScale,smallDefectEntry]
    field_simp [(defectRoot_pos (v j) 0).ne']
  simpa only [heq,zero_mul] using HH

lemma fderiv_eq_zero_of_coordDeriv_eq_zero {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hh : ∀ i, coordDeriv f i x=0) : fderiv ℝ f x=0 := by
  rw [← DeGiorgiCompactness.coordinateDual_fderiv]
  have he : (fun i => DeGiorgiCompactness.coordDeriv f i x) = 0 := funext hh
  rw [he,map_zero]

lemma fderiv_eq_of_coordDeriv_eq {n : ℕ} {f g : Space n → ℝ} {x : Space n}
    (hh : ∀ i, coordDeriv f i x=coordDeriv g i x) : fderiv ℝ f x=fderiv ℝ g x := by
  rw [← DeGiorgiCompactness.coordinateDual_fderiv,← DeGiorgiCompactness.coordinateDual_fderiv]
  congr 1
  funext i
  exact hh i

lemma coordDeriv_as_inner {n : ℕ} (f : Space n → ℝ) (i : Fin n) (x : Space n) :
    coordDeriv f i x = inner ℝ (gradient f x) (basis n i) := by
  rw [inner_gradient_left]
  rfl

theorem SmallDefectConverges.profile_limit {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (hv : ∀ j, v j ∈ positiveDefectClass n) (h0 : ∀ j, v j 0=0)
    (he : Tendsto (fun j => diffuseDefect (v j) 0) atTop (𝓝 0)) {ν : Space n}
    (hν : ∀ j, gradient (inverseProfile (v j)) 0 =
      Real.sqrt (1-diffuseDefect (v j) 0) • ν) :
    g none = fun x => inner ℝ ν x := by
  have hUU (i j : Fin n) (x : Space n) : coordDeriv (coordDeriv (g none) i) j x=0 := by
    have H := hg.at none [j,i] x
    simp only [normalizedSmallJet,smallDefectScale,smallDefectEntry,inv_one,one_mul,coordinateJet] at H
    exact tendsto_nhds_unique H (hg.tensor_vanishes hv he i j [] x)
  have hp_const (i : Fin n) (x : Space n) : coordDeriv (g none) i x=coordDeriv (g none) i 0 := by
    apply is_const_of_fderiv_eq_zero (coordDeriv_smooth (hg.1 none) i |>.differentiable (by simp))
      (fun x => fderiv_eq_zero_of_coordDeriv_eq_zero (fun j => hUU i j x)) x 0
  have hnorm : Tendsto (fun j => Real.sqrt (1-diffuseDefect (v j) 0)) atTop (𝓝 1) := by
    have H := Real.continuous_sqrt.continuousAt.tendsto.comp
      ((tendsto_const_nhds (x := (1 : ℝ))).sub he)
    simpa only [sub_zero,Real.sqrt_one,Function.comp_def] using H
  have hp0 (i : Fin n) : coordDeriv (g none) i 0=inner ℝ ν (basis n i) := by
    have HH := hnorm.mul_const (inner ℝ ν (basis n i))
    have H := hg.at none [i] 0
    simp only [normalizedSmallJet,smallDefectScale,smallDefectEntry,inv_one,one_mul,coordinateJet] at H
    have hh : (fun j => coordDeriv (inverseProfile (v j)) i 0) =
        fun j => Real.sqrt (1-diffuseDefect (v j) 0)*inner ℝ ν (basis n i) := by
      funext j
      rw [coordDeriv_as_inner,hν j,real_inner_smul_left]
    rw [hh] at H
    exact tendsto_nhds_unique H (by simpa only [one_mul] using HH)
  have hG0 : g none 0=0 := by
    have H := hg.at none [] 0
    have hh : (fun j => normalizedSmallJet (v j) none [] 0) = fun _ : ℕ => (0 : ℝ) := by
      funext j
      simp only [normalizedSmallJet,smallDefectScale,smallDefectEntry,coordinateJet,inv_one,one_mul,
        inverseProfile_zero (h0 j)]
    rw [hh] at H
    exact tendsto_nhds_unique H tendsto_const_nhds
  apply eq_of_fderiv_eq (hg.1 none |>.differentiable (by simp)) (innerSL ℝ ν).differentiable
    (fun x => fderiv_eq_of_coordDeriv_eq (fun i => ?_)) 0 (by simpa using hG0)
  rw [hp_const i x,hp0 i]
  simp only [coordDeriv, (innerSL ℝ ν).fderiv]
  rfl

lemma normalized_defect_limit_positive {n : ℕ} {v : ℕ → Space n → ℝ}
    (hv : ∀ j, ContDiff ℝ ∞ (v j))
    (hi : ∀ j x, v j x ∈ Set.Ioo (-1 : ℝ) 1) (hAC : ∀ j, AllenCahn (v j))
    (hp : ∀ j x, 0 < diffuseDefect (v j) x) {g : Space n → ℝ}
    (hg : TendstoLocallyUniformly
      (fun j x => (diffuseDefect (v j) 0)⁻¹ * diffuseDefect (v j) x) g atTop) :
    g 0 = 1 ∧ ∀ x, 0 < g x := by
  have ht (x : Space n) := hg.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ x)
  constructor
  · have hh : (fun j : ℕ => (diffuseDefect (v j) 0)⁻¹ * diffuseDefect (v j) 0) =
        fun _ => (1 : ℝ) := by
      funext j
      exact inv_mul_cancel₀ (hp j 0).ne'
    have H0 := ht 0
    rw [hh] at H0
    exact tendsto_nhds_unique H0 tendsto_const_nhds
  · intro x
    let K := Real.exp (relativeDefectConstant n * ‖x‖)
    have hK : 0 < K := Real.exp_pos _
    have hb (j : ℕ) : K⁻¹ ≤ (diffuseDefect (v j) 0)⁻¹ * diffuseDefect (v j) x := by
      have H := diffuseDefect_exp_comparison_crude (hv j) (hi j) (hAC j) (hp j) x 0
      simp only [zero_sub, norm_neg] at H
      change diffuseDefect (v j) 0 ≤ K * diffuseDefect (v j) x at H
      have H' : diffuseDefect (v j) 0 / K ≤ diffuseDefect (v j) x :=
        (div_le_iff₀ hK).mpr (by simpa [mul_comm] using H)
      have H'' := mul_le_mul_of_nonneg_left H' (inv_pos.mpr (hp j 0)).le
      have he : (diffuseDefect (v j) 0)⁻¹ * (diffuseDefect (v j) 0 / K) = K⁻¹ := by
        field_simp [(hp j 0).ne', hK.ne']
      rwa [he] at H''
    exact (inv_pos.mpr hK).trans_le (ge_of_tendsto (ht x) (Eventually.of_forall hb))

lemma SmallDefectConverges.at_U {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (l : List (Fin n)) (x : Space n) :
    Tendsto (fun j => coordinateJet (inverseProfile (v j)) l x) atTop
      (𝓝 (coordinateJet (g none) l x)) := by
  simpa only [normalizedSmallJet,smallDefectScale,smallDefectEntry,inv_one,one_mul] using hg.at none l x

lemma SmallDefectConverges.at_D {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (l : List (Fin n)) (x : Space n) :
    Tendsto (fun j => (diffuseDefect (v j) 0)⁻¹*coordinateJet (diffuseDefect (v j)) l x) atTop
      (𝓝 (coordinateJet (g (some none)) l x)) := hg.at (some none) l x

lemma SmallDefectConverges.at_T {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (a b : Fin n) (l : List (Fin n)) (x : Space n) :
    Tendsto (fun j => (defectRoot (v j) 0)⁻¹*coordinateJet (inverseHessian (v j) a b) l x) atTop
      (𝓝 (coordinateJet (g (some (some (a,b)))) l x)) := hg.at (some (some (a,b))) l x

end DeGiorgi
end

end OAI
