import OAI.Analysis.LienardCycles.BaseSymmetry

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.ReferenceCharacteristic
open ScalarArcs CanonicalVariation PolynomialModel WidthCoordinates
  WidthTransport PartialCalculus QuadraticCoordinates ArchSymmetries

noncomputable def base (q : (ℝ × ℝ) × ℝ) : ℝ :=
  baseAtWidth profile ((q.1,0),q.2)
noncomputable def J (q : (ℝ × ℝ) × ℝ) : ℝ := q.1.1+q.1.2*base q
noncomputable def A (q : (ℝ × ℝ) × ℝ) : ℝ := H ((J q,q.1.2),q.2)/q.2
noncomputable def D (q : (ℝ × ℝ) × ℝ) : ℝ := Hr ((J q,q.1.2),q.2)
noncomputable def Jz : (ℝ × ℝ) × ℝ → ℝ := direction ((1,0),0) J
noncomputable def Jk : (ℝ × ℝ) × ℝ → ℝ := direction ((0,1),0) J
noncomputable def Az : (ℝ × ℝ) × ℝ → ℝ := direction ((1,0),0) A
noncomputable def Ak : (ℝ × ℝ) × ℝ → ℝ := direction ((0,1),0) A
noncomputable def Dz : (ℝ × ℝ) × ℝ → ℝ := direction ((1,0),0) D
noncomputable def Dk : (ℝ × ℝ) × ℝ → ℝ := direction ((0,1),0) D

lemma base_analytic {q : (ℝ × ℝ) × ℝ} (hr : 0 < q.2) : ContDiffAt ℝ ω base q :=
  (WidthCoordinates.base_analytic profile profile_contDiff model_local_flow hr).comp q
    ((contDiffAt_fst.prodMk contDiffAt_const).prodMk contDiffAt_snd)
lemma J_analytic {q : (ℝ × ℝ) × ℝ} (hr : 0 < q.2) : ContDiffAt ℝ ω J q := by
  unfold J
  have hb := base_analytic hr
  fun_prop
lemma A_analytic {q : (ℝ × ℝ) × ℝ} (hr : 0 < q.2) : ContDiffAt ℝ ω A q := by
  exact ((H_analytic (d := J q) (k := q.1.2) hr).comp q
    (((J_analytic hr).prodMk contDiffAt_fst.snd).prodMk contDiffAt_snd)).div
      contDiffAt_snd (ne_of_gt hr)
lemma D_analytic {q : (ℝ × ℝ) × ℝ} (hr : 0 < q.2) : ContDiffAt ℝ ω D q :=
  (Hr_analytic (d := J q) (k := q.1.2) hr).comp q
    (((J_analytic hr).prodMk contDiffAt_fst.snd).prodMk contDiffAt_snd)

lemma Jz_hasDerivAt {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => J ((s,k),r)) (Jz ((z,k),r)) z :=
  slice_d ((J_analytic hr).differentiableAt (by simp))
lemma Jk_hasDerivAt {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => J ((z,s),r)) (Jk ((z,k),r)) k :=
  slice_k ((J_analytic hr).differentiableAt (by simp))
lemma Az_hasDerivAt {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => A ((s,k),r)) (Az ((z,k),r)) z :=
  slice_d ((A_analytic hr).differentiableAt (by simp))
lemma Ak_hasDerivAt {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => A ((z,s),r)) (Ak ((z,k),r)) k :=
  slice_k ((A_analytic hr).differentiableAt (by simp))
lemma Dz_hasDerivAt {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => D ((s,k),r)) (Dz ((z,k),r)) z :=
  slice_d ((D_analytic hr).differentiableAt (by simp))
lemma Dk_hasDerivAt {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => D ((z,s),r)) (Dk ((z,k),r)) k :=
  slice_k ((D_analytic hr).differentiableAt (by simp))

lemma A_abs_lt {q : (ℝ × ℝ) × ℝ} (hr : 0 < q.2) : |A q| < 1 := by
  dsimp [A]
  rw [abs_div,abs_of_pos hr,div_lt_one hr]
  exact H_abs_lt hr
lemma D_abs_lt {q : (ℝ × ℝ) × ℝ} (hr : 0 < q.2) : |D q| < 1 := Hr_abs_lt hr
lemma A_gap_pos {q : (ℝ × ℝ) × ℝ} (hr : 0 < q.2) : 0 < 1-(A q)^2 := by
  have ht := sq_lt_sq₀ (abs_nonneg (A q)) (by norm_num : (0:ℝ) ≤ 1) |>.mpr (A_abs_lt hr)
  nlinarith [sq_abs (A q)]
lemma D_gap_pos {q : (ℝ × ℝ) × ℝ} (hr : 0 < q.2) : 0 < 1-(D q)^2 := by
  have ht := sq_lt_sq₀ (abs_nonneg (D q)) (by norm_num : (0:ℝ) ≤ 1) |>.mpr (D_abs_lt hr)
  nlinarith [sq_abs (D q)]

lemma base_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => base ((z,k),s)) (-r*(1-(A ((z,k),r))^2)) r := by
  have hb := base_width_deriv profile profile_contDiff model_local_flow
    (p := (z,k)) (t := 0) hr
  rw [translation z k _ hr] at hb
  convert! hb using 1
  dsimp only [J,A,base]
  field_simp [ne_of_gt hr]

lemma J_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => J ((z,k),s)) (-k*r*(1-(A ((z,k),r))^2)) r := by
  convert! (base_deriv (z := z) (k := k) hr).const_mul k |>.const_add z using 1
  ring

lemma A_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => A ((z,k),s))
      (J ((z,k),r)*(1-(A ((z,k),r))^2)-2*A ((z,k),r)/r) r := by
  have hd := (((H_analytic (d := J ((z,k),r)) (k := k) hr).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (f := fun s => ((J ((z,k),s),k),s)) r
    (((J_deriv (z := z) (k := k) hr).prodMk (hasDerivAt_const r k)).prodMk (hasDerivAt_id r))).div
      (hasDerivAt_id r) (ne_of_gt hr)
  rw [fderiv_model] at hd
  have ht := width_identity (d := J ((z,k),r)) (k := k) hr
  change k*P ((J ((z,k),r),k),r)+J ((z,k),r)=
    (r*Hr ((J ((z,k),r),k),r)+H ((J ((z,k),r),k),r))/(r^2-H ((J ((z,k),r),k),r)^2) at ht
  have hg := ne_of_gt (H_gap_pos (d := J ((z,k),r)) (k := k) hr)
  convert! hd using 1
  dsimp [A,P,Hr,Q,direction] at ht ⊢
  field_simp [ne_of_gt hr,hg] at ht ⊢
  nlinarith [ht]

lemma D_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => D ((z,k),s))
      (2*A ((z,k),r)*(1-(D ((z,k),r))^2)/(r*(1-(A ((z,k),r))^2))) r := by
  have hd := (Hr_analytic (d := J ((z,k),r)) (k := k) hr).differentiableAt (by simp)
  have hc := hd.hasFDerivAt.comp_hasDerivAt (f := fun s => ((J ((z,k),s),k),s)) r
    (((J_deriv (z := z) (k := k) hr).prodMk (hasDerivAt_const r k)).prodMk (hasDerivAt_id r))
  rw [fderiv_model] at hc
  have hR : direction ((1,0),0) Hr ((J ((z,k),r),k),r)=R ((J ((z,k),r),k),r) :=
    direction_comm (H_analytic hr) _ _
  rw [hR] at hc
  have ht := transport_Hr (d := J ((z,k),r)) (k := k) hr
  have hg := ne_of_gt (H_gap_pos (d := J ((z,k),r)) (k := k) hr)
  have ha := ne_of_gt (A_gap_pos (q := ((z,k),r)) hr)
  convert! hc using 1
  dsimp [A,D,Hrr,alpha,gap] at ht ⊢
  field_simp [ne_of_gt hr,hg] at ht ⊢
  nlinarith [ht]

end QuinticLienard.ReferenceCharacteristic

end OAI
