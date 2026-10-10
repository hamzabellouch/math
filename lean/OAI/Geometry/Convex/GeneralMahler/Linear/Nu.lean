import OAI.Geometry.Convex.GeneralMahler.Linear.Segments

namespace OAI
/-! Positive endpoint functional Nu. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open HMode Profile Layers Segment
variable {m:ℕ}
namespace LPt
variable (M:Mat m) (l:Fin m→ℝ)
def npt (f:Plane→ℝ) :=
  mats (fun i=>∑ j,M i j^2*f (l i,l j))
def mout (f:Plane→ℝ) : Mat m :=
  Matrix.of fun i j=>M i j*f (l i,l j)

lemma n_add (f g:Plane→ℝ) : npt M l (fun u=>f u+g u)=npt M l f+npt M l g := by
  simp_rw [npt,mul_add,Finset.sum_add_distrib]
  apply mats_add
lemma n_sub (f g:Plane→ℝ) : npt M l (fun u=>f u-g u)=npt M l f-npt M l g := by
  have he := n_add M l (fun u=>f u-g u) g
  have hh : (fun u=>f u-g u+g u)=f := by ext; ring
  rw [hh] at he; linarith
lemma n_s (a:ℝ) (f:Plane→ℝ) :
    npt M l (fun u=>a*f u)=a*npt M l f := by
  unfold npt
  simp_rw [mul_left_comm (_^2:ℝ), ← Finset.mul_sum]; apply mats_s
lemma n_flip (u:Plane→ℝ) (hm:M.IsHermitian) :
    npt M l (fun x:Plane=>u x.swap) = npt M l u := by
  unfold npt mats
  congr 1; rw [Finset.sum_comm]; apply Finset.sum_congr rfl
  intro i _; apply Finset.sum_congr rfl; intro j _
  rw [symm_entry hm]; rfl
lemma hsout (f:Plane→ℝ) :
    hsN (mout M l f)= npt M l (fun u=> f u^2) := by
  rw [hsN_eq,npt]; congr 1
  ext; simp only [mout,Matrix.of_apply,mul_pow]

lemma ipnout (f:Plane→ℝ) :
    ipN M (mout M l f) = npt M l f := by
  rw [ipN_ent,npt]; congr 1; ext
  simp only [mout,Matrix.of_apply,pow_two,mul_assoc]

lemma out_her (f:ℝ→ℝ) (hf:TestF f) (hm:M.IsHermitian) :
    (mout M l (bav f)).IsHermitian := by
  change star _=_
  ext i j
  change M j i *bav f (l j,l i)=M i j*bav f (l i,l j)
  rw [symm_entry hm j i]
  rw [show bav f (l j,l i)=_ from bav_sym hf (l i,l j)]
end LPt
namespace ProjField
open LPt
variable [NeZero m] (q:ProjField m)
def nupt (i:Fin m) (x:Rn m) : (Plane→ℝ)→ℝ :=
  npt ((q.FL.Fr x).loc (q.M i)) (q.FL.ev x)
def nu (f:Plane→ℝ) :=
  ∑ i:Fin m,(∫ x,q.nupt i x f ∂normal m)

-- measurable rotation argument
omit [NeZero m] in
lemma ContLoc (A:Mat m): Continuous (fun u:Frm m=> u.loc A) := by
  let k := fun u:Frm m=>u.val
  have hk : Continuous k := continuous_subtype_val
  exact (hk.star.mul (show Continuous (fun _:Frm m=>A) from continuous_const)).mul hk
omit [NeZero m] in
lemma MeasLoc (f:Rn m→Frm m) (hf:Measurable f) (A:Mat m):
    Measurable (fun x=> (f x).loc A) := (ContLoc A).measurable.comp hf
lemma locMe (_i:Fin m) (A:Mat m):
    regular (fun x:Rn m=> (q.FL.Fr x).loc A) := by
  constructor
  · apply PolyBound.of_bound ‖A‖
    intro x; rw [Frm.loc_norm]
  have he : Continuous (fun u:Frm m=> u.loc A) := ContLoc A
  have hm : Measurable (fun x:Rn m=> (q.FL.Fr x).loc A) := MeasLoc q.FL.Fr q.FL.fr_m A
  exact hm.aestronglyMeasurable
lemma nu_i {f:Plane→ℝ} (hf:Bwt f) (i:Fin m) :
    Integrable (fun x=> q.nupt i x f) (normal m) := by
  let l := q.FL.ev
  let M := fun x=> (q.FL.Fr x).loc (q.M i)
  have hi (j k:Fin m) : regular (fun x:Rn m=> (M x j k)^2*f (l x j,l x k)) := by
    have he := ((q.locMe i (q.M i)).lin (coeffMap j k))
    have hp : regular (fun x:Rn m=> f (l x j, l x k)) :=
      ⟨hf.p.comp ((poly_eig q.FL.poly q.FL.Fr j).prodMk (poly_eig q.FL.poly q.FL.Fr k)),
        (hf.c.measurable.comp ((q.FL.ev_m j).prodMk (q.FL.ev_m k))).aestronglyMeasurable⟩
    simp_rw [pow_two]
    exact (he.mul he).mul hp
  unfold nupt LPt.npt mats
  refine Integrable.div_const (integrable_finsetSum _ ?_) _
  exact fun j _=> integrable_finsetSum _ (fun k _=> (hi j k).ig)
lemma nu_add {f g:Plane→ℝ} (hf:Bwt f) (hg:Bwt g) :
    q.nu (fun u=>f u+g u)=q.nu f+q.nu g := by
  have he (i:Fin m) (x:Rn m) :
    q.nupt i x (fun u=>f u+g u)=q.nupt i x f+q.nupt i x g:= n_add ..
  unfold nu; simp_rw [he,integral_add (q.nu_i hf _) (q.nu_i hg _),Finset.sum_add_distrib]
lemma nu_sub {f g:Plane→ℝ} (hf:Bwt f) (hg:Bwt g) :
    q.nu (fun u=>f u-g u)=q.nu f-q.nu g := by
  have he := q.nu_add (hf.sub hg) hg
  rw [show (fun x=>f x-g x+g x)=f by ext; ring] at he; linarith
lemma nu_s (f:Plane→ℝ) (a:ℝ) :
    q.nu (fun u=>a*f u)=a*q.nu f := by
  unfold nu nupt; simp_rw [n_s,integral_const_mul,← Finset.mul_sum]
lemma nu_flip (f:Plane→ℝ) :
    q.nu (fun x:Plane=>f x.swap)=q.nu f := by
  unfold nu nupt
  simp_rw [n_flip _ _ f ((q.FL.Fr _).HL (q.M_sym _))]
end ProjField
end GeneralMahler

end

end OAI
