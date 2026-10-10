import OAI.Geometry.Convex.GeneralMahler.Contact

namespace OAI
/-! Eq13 covariance equals Q+Ct on centered tests. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric Matrix
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open HMode Layers Profile
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m)

omit [NeZero m] in
lemma mixed_contract {f j:ℝ→Rn m→Rn m} (hf:mixed f) (hj:mixed j) :
    mixed fun u:Plane=>fun x=> ⟪f u.1 x,j u.2 x⟫ := by
  intro n
  obtain ⟨C,l,hc,h⟩ := hf n
  obtain ⟨D,k,hd,h'⟩ := hj n
  use C*D,l+k,mul_nonneg hc hd
  intro u y
  have ha : (1+‖u‖)^n ≤ (1+‖u.1‖)^n*(1+‖u.2‖)^n := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    change 1+max _ _ ≤ _
    rcases max_choice ‖u.1‖ ‖u.2‖ with h|h <;> rw [h] <;> nlinarith [norm_nonneg u.1,norm_nonneg u.2]
  apply le_trans (mul_le_mul (abs_real_inner_le_norm (f u.1 y) (j u.2 y)) ha (by positivity)
    (by positivity))
  calc
    _ = (‖f u.1 y‖*(1+‖u.1‖)^n)*(‖j u.2 y‖*(1+‖u.2‖)^n) := by ring
    _ ≤ _ := mul_le_mul (h _ _) (h' _ _) (by positivity) (by positivity)
    _ = _ := by rw [pow_add]; ring

lemma ipt_double {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) :
    ipt (q.WH f) (q.WH g) =
      ∫ u:Plane,ipt (q.WW u.1) (q.WW u.2)*(deriv f u.1*deriv g u.2) ∧
    Integrable fun u:Plane=>ipt (q.WW u.1) (q.WW u.2)*(deriv f u.1*deriv g u.2) := by
  let C := fun u:Plane=>fun x=>⟪q.WK f u.1 x,q.WK g u.2 x⟫
  have hC : mixed C := mixed_contract (q.WK_m hf) (q.WK_m hg)
  have hm : StronglyMeasurable C.uncurry :=
    ((q.WK_SM f).comp_measurable
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).inner
        ((q.WK_SM g).comp_measurable
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hi := mixed_integrable (μ:=volume) (ν:=normal m) hC hm.aestronglyMeasurable
  have he (u:Plane) :
      ipt (q.WW u.1) (q.WW u.2)*(deriv f u.1*deriv g u.2) =
        (∫ x,C u x ∂normal m)/(m:ℝ) := by
    have hh (x) : C u x=(deriv f u.1*deriv g u.2)*⟪q.WW u.1 x,q.WW u.2 x⟫ := by
      unfold C WK; rw [real_inner_smul_left,real_inner_smul_right]; ring
    simp_rw [hh]
    rw [integral_const_mul]
    unfold ipt; ring
  simp_rw [he]
  refine ⟨?_,hi.integral_prod_left.div_const _⟩
  rw [integral_div,integral_integral_swap hi]
  have iW (f:ℝ→ℝ) (hf:TestF f) (x) : Integrable (fun z=> q.WK f z x) :=
    mixed_integrable_left (q.WK_m hf) x
      (((q.WK_SM f).comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  unfold ipt WH
  congr 2
  ext x
  have hi : Integrable (fun u:Plane=> C u x) := mixed_integrable_left hC x
    ((hm.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  exact (integral_prod_bilin (innerSL ℝ) (iW f hf x) (iW g hg x)).symm

lemma Ct_integrable {f g} (hf:TestF f) (hg:TestF g) :
    Integrable fun u:Plane=>q.ct u*(deriv f u.1*deriv g u.2) := by
  let T := fun u:Plane=> deriv f u.1*deriv g u.2
  have hi := (q.ipt_double hf hg).2
  have hh := (q.H_cov_I hf hg).1
  have hu : Integrable fun u:Plane=> q.Lr.Kab u*T u :=
    q.Lr.Kab_I ((hf.der.cont.comp continuous_fst).mul (hg.der.cont.comp continuous_snd))
      ((hf.der.poly.comp PolyBound.fst).mul (hg.der.poly.comp PolyBound.snd))
  convert (hi.add hu).sub hh using 1
  ext x
  change q.ct x*T x = _+_-_
  dsimp only
  rw [show ipt (q.WW x.1) (q.WW x.2)=_ from q.WW_pair_cov x]
  unfold T; ring

lemma eq13 {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) (hF:ga f=0) (hG:ga g=0) :
    KP q.covMat (q.Hmat f) (q.Hmat g)=q.Lr.Q f g+q.Ct f g := by
  have hu : Integrable fun u:Plane=> q.Lr.Kab u*(deriv f u.1*deriv g u.2) :=
    q.Lr.Kab_I ((hf.der.cont.comp continuous_fst).mul (hg.der.cont.comp continuous_snd))
      ((hf.der.poly.comp PolyBound.fst).mul (hg.der.poly.comp PolyBound.snd))
  have hi := q.H_cov_I hf hg; rw [hF,hG] at hi
  simp only [sub_zero] at hi
  have he := q.Lr.R_identity hf hg
  rw [← q.pt_k_cov hf hg,show (∫ x, ⟪q.WH f x,q.WH g x⟫ ∂normal m)/(m:ℝ)= _
    from (q.ipt_double hf hg).1]
  simp_rw [q.WW_pair_cov,sub_mul,add_mul]
  have hc := q.Ct_integrable hf hg
  rw [integral_sub,integral_add hi.1 hc,hi.2,he]
  · have hh : q.Lr.mrg=q.layerW := by ext; unfold layerW rightLayer.mrg Lr; ring
    rw [hh]; unfold Ct; ring
  · exact hi.1.add hc
  exact hu
end ProjField
end GeneralMahler

end

end OAI
