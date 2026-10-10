import OAI.Geometry.QuadricBundles.Plurisubharmonic

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29

namespace QuadricCounterexample
open Set Filter Topology
open scoped Matrix.Norms.Elementwise
noncomputable section

lemma fderiv_apply_const {X : Type u1} {Y : Type u2} {Z : Type u3} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : X → Y →L[ℝ] Z} {x : X} (hF : DifferentiableAt ℝ F x) (v : Y) :
    fderiv ℝ (fun y ↦ F y v) x =
      (ContinuousLinearMap.apply ℝ Z v).comp (fderiv ℝ F x) := by
  exact ((ContinuousLinearMap.apply ℝ Z v).hasFDerivAt.comp x hF.hasFDerivAt).fderiv

lemma hessian_mul {X : Type u4} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f g : X → ℂ} {x : X} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (v w : X) :
    fderiv ℝ (fderiv ℝ (fun y ↦ f y*g y)) x v w =
      fderiv ℝ (fderiv ℝ f) x v w*g x + fderiv ℝ f x w*fderiv ℝ g x v +
      fderiv ℝ f x v*fderiv ℝ g x w + f x*fderiv ℝ (fderiv ℝ g) x v w := by
  have hf1 := hf.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hg1 := hg.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hf2 := (hf.fderiv_right (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hg2 := (hg.fderiv_right (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hf' := hf2.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have hg' := hg2.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have hfg2 := ((hf.mul hg).fderiv_right (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have he : (fun y ↦ fderiv ℝ (fun z ↦ f z*g z) y w) =ᶠ[𝓝 x]
      fun y ↦ f y * fderiv ℝ g y w + g y * fderiv ℝ f y w := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with y hy hy'
    change (fderiv ℝ (f*g) y) w = _
    rw [fderiv_mul (hy.differentiableAt (by norm_num)) (hy'.differentiableAt (by norm_num))]
    simp
  have hh := (hf1.hasFDerivAt.mul hg').add (hg1.hasFDerivAt.mul hf')
  have hx := congrArg (fun T : X →L[ℝ] ℂ ↦ T v) (he.fderiv_eq.trans hh.fderiv)
  rw [fderiv_apply_const hfg2] at hx
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,
    add_apply,smul_apply,
    ContinuousLinearMap.comp_zero,zero_add,smul_eq_mul,
    ContinuousLinearMap.flip_apply] at hx
  convert hx using 1; ring

lemma hessian_re {X : Type u5} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℂ} {x : X} (hf : ContDiffAt ℝ 2 f x) (v w : X) :
    fderiv ℝ (fderiv ℝ (fun y ↦ (f y).re)) x v w =
      (fderiv ℝ (fderiv ℝ f) x v w).re := by
  have hf1 := hf.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hf2 := (hf.fderiv_right (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have he : (fun y ↦ fderiv ℝ (fun z ↦ (f z).re) y w) =ᶠ[𝓝 x]
      fun y ↦ (fderiv ℝ f y w).re := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact congrArg (fun T : X →L[ℝ] ℝ ↦ T w)
      (Complex.reCLM.hasFDerivAt.comp y
        (hy.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hh := Complex.reCLM.hasFDerivAt.comp x
    (hf2.hasFDerivAt.clm_apply (hasFDerivAt_const w x))
  have hx := congrArg (fun T : X →L[ℝ] ℝ ↦ T v) (he.fderiv_eq.trans hh.fderiv)
  have hq2 : DifferentiableAt ℝ (fderiv ℝ (fun y ↦ (f y).re)) x := ((Complex.reCLM.contDiff.contDiffAt.comp x hf).fderiv_right
    (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt
      (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  rw [fderiv_apply_const hq2] at hx
  simpa using hx

lemma hessian_clm {X : Type u6} {Y : Type u7} {Z : Type u8}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : X → Y} {x : X} (hf : ContDiffAt ℝ 2 f x) (L : Y →L[ℝ] Z) (v w : X) :
    fderiv ℝ (fderiv ℝ (fun y ↦ L (f y))) x v w =
      L (fderiv ℝ (fderiv ℝ f) x v w) := by
  have hf2 := (hf.fderiv_right (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have he : (fun y ↦ fderiv ℝ (fun z ↦ L (f z)) y w) =ᶠ[𝓝 x]
      fun y ↦ L (fderiv ℝ f y w) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact congrArg (fun T : X →L[ℝ] Z ↦ T w)
      (L.hasFDerivAt.comp y (hy.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hh := L.hasFDerivAt.comp x
    (hf2.hasFDerivAt.clm_apply (hasFDerivAt_const w x))
  have hx := congrArg (fun T : X →L[ℝ] Z ↦ T v) (he.fderiv_eq.trans hh.fderiv)
  have hq2 : DifferentiableAt ℝ (fderiv ℝ (fun y ↦ L (f y))) x :=
    ((L.contDiff.contDiffAt.comp x hf).fderiv_right
      (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  rw [fderiv_apply_const hq2] at hx
  simpa using hx

lemma hessian_sum {X : Type u9} {Y : Type u10} {ι : Type u11}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : ι → X → Y} {x : X} {s : Finset ι}
    (hf : ∀ i∈s, ContDiffAt ℝ 2 (f i) x) (v w : X) :
    fderiv ℝ (fderiv ℝ (fun y ↦ ∑ i∈s, f i y)) x v w =
      ∑ i∈s, fderiv ℝ (fderiv ℝ (f i)) x v w := by
  have hf1 i hi := (hf i hi).differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hf2 i hi := ((hf i hi).fderiv_right (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have he : fderiv ℝ (fun y ↦ ∑ i∈s, f i y) =ᶠ[𝓝 x]
      fun y ↦ ∑ i∈s, fderiv ℝ (f i) y := by
    have hen : ∀ᶠ y in 𝓝 x, ∀ i∈s, ContDiffAt ℝ 2 (f i) y := by
      simpa only [Filter.eventually_all_finset] using
        (show ∀ i∈s, ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 (f i) y from
          fun i hi ↦ (hf i hi).eventually (by norm_num))
    filter_upwards [hen] with y hy
    exact fderiv_fun_sum fun i hi ↦ (hy i hi).differentiableAt (by norm_num)
  have hh := fderiv_fun_sum hf2
  rw [he.fderiv_eq, hh]
  simp

lemma hessian_pullback_clm {X : Type u12} {Y : Type u13} {Z : Type u14}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : Y → Z} (L : X →L[ℝ] Y) {x : X} (hf : ContDiffAt ℝ 2 f (L x)) (v w : X) :
    fderiv ℝ (fderiv ℝ (fun y ↦ f (L y))) x v w =
      fderiv ℝ (fderiv ℝ f) (L x) (L v) (L w) := by
  change fderiv ℝ (fderiv ℝ (f ∘ L)) x v w = _
  rw [hessian_comp_apply L.contDiff.contDiffAt hf]
  have he : fderiv ℝ L = fun _ ↦ L := funext fun y ↦ L.fderiv
  simp [he]

lemma hessian_linear_zero {X : Type u15} {Y : Type u16} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (L : X →L[ℝ] Y) (x v w : X) :
    fderiv ℝ (fderiv ℝ L) x v w = 0 := by
  have he : fderiv ℝ L = fun _ ↦ L := funext fun y ↦ L.fderiv
  simp [he]

lemma hessian_linear_mul_linear {X : Type u17} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℂ} {x : X} (hf : ContDiffAt ℝ 2 f x)
    (L M : X →L[ℝ] ℂ) (v : X) :
    fderiv ℝ (fderiv ℝ (fun y ↦ L y * f y * M y)) x v v =
      L x * (fderiv ℝ (fderiv ℝ f) x v v) * M x +
      2 * L v * fderiv ℝ f x v * M x +
      2 * L x * fderiv ℝ f x v * M v + 2 * L v * f x * M v := by
  rw [hessian_mul (L.contDiff.contDiffAt.mul hf) M.contDiff.contDiffAt,
    hessian_mul L.contDiff.contDiffAt hf,hessian_linear_zero,hessian_linear_zero]
  have hd := fderiv_fun_mul L.differentiableAt
    (hf.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0))
  have hd' : fderiv ℝ (fun y ↦ L y * f y) x =
      L x • fderiv ℝ f x + f x • L := by simpa only [L.fderiv] using hd
  rw [hd']
  simp only [L.fderiv,M.fderiv,add_apply,smul_apply,smul_eq_mul]
  ring

section Quadratic
variable {X : Type u18} {ι : Type u19} [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype ι]

def entryCLM (i j : ι) : Matrix ι ι ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj j : (ι → ℂ) →L[ℝ] ℂ).comp
    (ContinuousLinearMap.proj i : Matrix ι ι ℂ →L[ℝ] (ι → ℂ))

def fiberEntryCLM (i : ι) : (X × (ι → ℂ)) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ X (ι → ℂ))

def starFiberEntryCLM (i : ι) : (X × (ι → ℂ)) →L[ℝ] ℂ :=
  Complex.conjCLE.toContinuousLinearMap.comp (fiberEntryCLM i)

lemma base_entry_C2 {H : X → Matrix ι ι ℂ} {z : X}
    (hH : ContDiffAt ℝ 2 H z) (v : ι → ℂ) (i j : ι) :
    ContDiffAt ℝ 2 (fun p : X × (ι → ℂ) ↦ H p.1 i j) (z,v) :=
  (entryCLM i j).contDiff.contDiffAt.comp (z,v) (hH.comp (z,v) contDiff_fst.contDiffAt)

lemma base_entry_fderiv {H : X → Matrix ι ι ℂ} {z : X}
    (hH : ContDiffAt ℝ 2 H z) (v : ι → ℂ) (i j : ι) (u : X) (w : ι → ℂ) :
    fderiv ℝ (fun p : X × (ι → ℂ) ↦ H p.1 i j) (z,v) (u,w) =
      fderiv ℝ H z u i j := by
  have hh := (entryCLM i j).hasFDerivAt.comp (z,v)
    ((hH.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).hasFDerivAt.comp (z,v)
      (ContinuousLinearMap.fst ℝ X (ι → ℂ)).hasFDerivAt)
  convert congrArg (fun T ↦ T (u,w)) hh.fderiv using 1 <;> rfl

lemma base_entry_hessian {H : X → Matrix ι ι ℂ} {z : X}
    (hH : ContDiffAt ℝ 2 H z) (v : ι → ℂ) (i j : ι) (u : X) (w : ι → ℂ) :
    fderiv ℝ (fderiv ℝ (fun p : X × (ι → ℂ) ↦ H p.1 i j)) (z,v) (u,w) (u,w) =
      fderiv ℝ (fderiv ℝ H) z u u i j := by
  have he := hessian_pullback_clm (f := fun y ↦ H y i j)
    (x := (z,v)) (ContinuousLinearMap.fst ℝ X (ι → ℂ))
    ((entryCLM i j).contDiff.contDiffAt.comp z hH) (u,w) (u,w)
  have hh := hessian_clm hH (entryCLM i j) u u
  exact he.trans hh

def complexQuadratic (H : X → Matrix ι ι ℂ) (p : X × (ι → ℂ)) : ℂ :=
  star p.2 ⬝ᵥ ((H p.1).mulVec p.2)

def hermitianQuadratic (H : X → Matrix ι ι ℂ) (p : X × (ι → ℂ)) : ℝ :=
  (complexQuadratic H p).re

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
lemma complexQuadratic_eq_sum (H : X → Matrix ι ι ℂ) :
    complexQuadratic H = fun p ↦ ∑ i, ∑ j, star (p.2 i)*H p.1 i j*p.2 j := by
  funext p
  simp only [complexQuadratic,dotProduct,Matrix.mulVec,Pi.star_apply,
    Finset.mul_sum,mul_assoc]

lemma complexQuadratic_C2 {H : X → Matrix ι ι ℂ} {z : X}
    (hH : ContDiffAt ℝ 2 H z) (v : ι → ℂ) :
    ContDiffAt ℝ 2 (complexQuadratic H) (z,v) := by
  rw [complexQuadratic_eq_sum]
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact ((starFiberEntryCLM i).contDiff.contDiffAt.mul
    (base_entry_C2 hH v i j)).mul (fiberEntryCLM j).contDiff.contDiffAt

lemma complexQuadratic_hessian {H : X → Matrix ι ι ℂ} {z : X}
    (hH : ContDiffAt ℝ 2 H z) (v : ι → ℂ) (u : X) (w : ι → ℂ) :
    fderiv ℝ (fderiv ℝ (complexQuadratic H)) (z,v) (u,w) (u,w) =
      star v ⬝ᵥ ((fderiv ℝ (fderiv ℝ H) z u u).mulVec v) +
      2 * (star w ⬝ᵥ ((fderiv ℝ H z u).mulVec v)) +
      2 * (star v ⬝ᵥ ((fderiv ℝ H z u).mulVec w)) +
      2 * (star w ⬝ᵥ ((H z).mulVec w)) := by
  have ht i j : ContDiffAt ℝ 2
      (fun p : X × (ι → ℂ) ↦ star (p.2 i)*H p.1 i j*p.2 j) (z,v) :=
    ((starFiberEntryCLM i).contDiff.contDiffAt.mul
      (base_entry_C2 hH v i j)).mul (fiberEntryCLM j).contDiff.contDiffAt
  have hh (i j : ι) := hessian_linear_mul_linear (base_entry_C2 hH v i j)
    (starFiberEntryCLM i) (fiberEntryCLM j) (u,w)
  simp only [base_entry_hessian hH,base_entry_fderiv hH] at hh
  rw [complexQuadratic_eq_sum,hessian_sum (fun i _ ↦ ContDiffAt.sum (fun j _ ↦ ht i j))]
  simp_rw [hessian_sum (fun j _ ↦ ht _ j)]
  change (∑ i, ∑ j, _) = _
  calc
    _ = ∑ i, ∑ j,
      (star (v i)*(fderiv ℝ (fderiv ℝ H) z u u i j)*v j +
      2*star (w i)*(fderiv ℝ H z u i j)*v j +
      2*star (v i)*(fderiv ℝ H z u i j)*w j + 2*star (w i)*H z i j*w j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hh i j
    _ = _ := by
      simp only [dotProduct,Matrix.mulVec,Pi.star_apply,Finset.sum_add_distrib,
        Finset.mul_sum,mul_assoc]

end Quadratic

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology
open scoped Matrix.Norms.Elementwise ComplexOrder
noncomputable section

def matrixAdjointCLM {ι : Type u20} [Fintype ι] :
    Matrix ι ι ℂ →L[ℝ] Matrix ι ι ℂ where
  toFun := Matrix.conjTranspose
  map_add' := Matrix.conjTranspose_add
  map_smul' r M := by ext i j; simp [Matrix.conjTranspose_apply]
  cont := continuous_id.matrix_conjTranspose

lemma hermitian_fderiv {X : Type u21} {ι : Type u22} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype ι] {H : X → Matrix ι ι ℂ} {z : X}
    (hH : DifferentiableAt ℝ H z) (hh : ∀ᶠ y in 𝓝 z, (H y).IsHermitian) (u : X) :
    (fderiv ℝ H z u).IsHermitian := by
  have he : (fun y ↦ matrixAdjointCLM (H y)) =ᶠ[𝓝 z] H := hh
  have hd := matrixAdjointCLM.hasFDerivAt.comp z hH.hasFDerivAt
  have heq := hd.fderiv.symm.trans he.fderiv_eq
  exact congrArg (fun T ↦ T u) heq

lemma hermitian_hessian {X : Type u23} {ι : Type u24} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype ι] {H : X → Matrix ι ι ℂ} {z : X}
    (hH : ContDiffAt ℝ 2 H z) (hh : ∀ᶠ y in 𝓝 z, (H y).IsHermitian) (u v : X) :
    (fderiv ℝ (fderiv ℝ H) z u v).IsHermitian := by
  have hf2 := (hH.fderiv_right (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hd := hf2.hasFDerivAt.clm_apply (hasFDerivAt_const v z)
  have he : (fderiv ℝ (fun y ↦ fderiv ℝ H y v) z) u =
      fderiv ℝ (fderiv ℝ H) z u v := by
    convert congrArg (fun L : X →L[ℝ] Matrix ι ι ℂ ↦ L u) hd.fderiv using 1 <;> try rfl
    simp only [ContinuousLinearMap.comp_zero,zero_add]
    rfl
  rw [← he]
  apply hermitian_fderiv hd.differentiableAt
  filter_upwards [hH.eventually (by norm_num),hh.eventually_nhds] with y hy hy'
  exact hermitian_fderiv (hy.differentiableAt (by norm_num)) hy' v

end
end QuadricCounterexample

namespace QuadricCounterexample
open Matrix
open scoped ComplexOrder
noncomputable section

lemma matrix_completed_square {n : Type u25} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.PosDef) (A T : Matrix n n ℂ) (v w : n → ℂ) :
    star v ⬝ᵥ (T.mulVec v) + star w ⬝ᵥ (A.mulVec v) +
      star v ⬝ᵥ (A.conjTranspose.mulVec w) + star w ⬝ᵥ (H.mulVec w) =
    star v ⬝ᵥ ((T-A.conjTranspose*H⁻¹*A).mulVec v) +
      star (w+H⁻¹.mulVec (A.mulVec v)) ⬝ᵥ (H.mulVec (w+H⁻¹.mulVec (A.mulVec v))) := by
  have hi : H*H⁻¹=1 := H.mul_nonsing_inv (H.isUnit_iff_isUnit_det.mp hH.isUnit)
  have hi' : H⁻¹*H=1 := H.nonsing_inv_mul (H.isUnit_iff_isUnit_det.mp hH.isUnit)
  have hs : H⁻¹.conjTranspose = H⁻¹ := hH.inv.isHermitian
  have hb : H.mulVec (H⁻¹.mulVec (A.mulVec v)) = A.mulVec v := by
    rw [mulVec_mulVec,hi,one_mulVec]
  have hc (y : n → ℂ) : star (H⁻¹.mulVec (A.mulVec v)) ⬝ᵥ (H.mulVec y) =
      star v ⬝ᵥ (A.conjTranspose.mulVec y) := by
    simp only [star_mulVec,hs,dotProduct_mulVec,vecMul_vecMul,mul_assoc,hi',mul_one]
  simp only [mulVec_add,star_add,dotProduct_add,add_dotProduct,hb,hc,
    sub_mulVec,dotProduct_sub]
  have hh := hc (H⁻¹.mulVec (A.mulVec v))
  rw [hb] at hh
  rw [hh]
  simp only [mulVec_mulVec,mul_assoc]
  ring

lemma matrix_completed_square_nonneg {n : Type u26} [Fintype n] [DecidableEq n]
    {H A T : Matrix n n ℂ} (hH : H.PosDef)
    (hT : (T-A.conjTranspose*H⁻¹*A).PosSemidef) (v w : n → ℂ) :
    0 ≤ (star v ⬝ᵥ (T.mulVec v) + star w ⬝ᵥ (A.mulVec v) +
      star v ⬝ᵥ (A.conjTranspose.mulVec w) + star w ⬝ᵥ (H.mulVec w)).re := by
  rw [matrix_completed_square hH]
  exact (Complex.nonneg_iff.mp (add_nonneg
    (hT.dotProduct_mulVec_nonneg v)
    (hH.posSemidef.dotProduct_mulVec_nonneg _))).1

end
end QuadricCounterexample

namespace QuadricCounterexample
open Matrix
noncomputable section

lemma quadratic_levi_expansion {ι : Type u27} [Fintype ι]
    (H D E U V : Matrix ι ι ℂ) (hD : D.IsHermitian) (hE : E.IsHermitian)
    (v w : ι → ℂ) :
    (star v ⬝ᵥ U.mulVec v + 2 * (star w ⬝ᵥ D.mulVec v) +
      2 * (star v ⬝ᵥ D.mulVec w) + 2 * (star w ⬝ᵥ H.mulVec w)) +
    (star v ⬝ᵥ V.mulVec v + 2 * (star (Complex.I • w) ⬝ᵥ E.mulVec v) +
      2 * (star v ⬝ᵥ E.mulVec (Complex.I • w)) +
      2 * (star (Complex.I • w) ⬝ᵥ H.mulVec (Complex.I • w))) =
    4 * (star v ⬝ᵥ ((1/4 : ℂ) • (U+V)).mulVec v +
      star w ⬝ᵥ ((1/2 : ℂ) • (D-Complex.I • E)).mulVec v +
      star v ⬝ᵥ (((1/2 : ℂ) • (D-Complex.I • E)).conjTranspose).mulVec w +
      star w ⬝ᵥ H.mulVec w) := by
  have hs : ((1/2 : ℂ) • (D-Complex.I • E)).conjTranspose =
      (1/2 : ℂ) • (D+Complex.I • E) := by
    simp only [conjTranspose_smul,conjTranspose_sub, hD.eq,hE.eq]
    simp
  rw [hs]
  simp only [star_smul,Complex.star_def,Complex.conj_I,
    mulVec_smul,smul_mulVec,smul_dotProduct,dotProduct_smul,smul_eq_mul,
    add_mulVec,sub_mulVec,dotProduct_add,dotProduct_sub]
  ring_nf
  simp only [Complex.I_sq, mul_neg, mul_one]
  ring

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ComplexOrder
noncomputable section
variable {X : Type u28} {ι : Type u29} [NormedAddCommGroup X] [NormedSpace ℂ X] [Fintype ι]

def wirtingerDerivative (H : X → Matrix ι ι ℂ) (z u : X) : Matrix ι ι ℂ :=
  (1/2 : ℂ) • (fderiv ℝ H z u - Complex.I • fderiv ℝ H z (Complex.I • u))

def mixedHessian (H : X → Matrix ι ι ℂ) (z u : X) : Matrix ι ι ℂ :=
  (1/4 : ℂ) • (fderiv ℝ (fderiv ℝ H) z u u +
    fderiv ℝ (fderiv ℝ H) z (Complex.I • u) (Complex.I • u))

lemma hermitianQuadratic_C2 {H : X → Matrix ι ι ℂ} {z : X}
    (hH : ContDiffAt ℝ 2 H z) (v : ι → ℂ) :
    ContDiffAt ℝ 2 (hermitianQuadratic H) (z,v) :=
  Complex.reCLM.contDiff.contDiffAt.comp (z,v) (complexQuadratic_C2 hH v)

lemma hermitianQuadratic_levi {H : X → Matrix ι ι ℂ} {z : X}
    (hH : ContDiffAt ℝ 2 H z) (hh : ∀ᶠ y in 𝓝 z, (H y).IsHermitian)
    (v : ι → ℂ) (u : X) (w : ι → ℂ) :
    leviTrace (hermitianQuadratic H) (z,v) (u,w) =
      4 * (star v ⬝ᵥ (mixedHessian H z u).mulVec v +
        star w ⬝ᵥ (wirtingerDerivative H z u).mulVec v +
        star v ⬝ᵥ (wirtingerDerivative H z u).conjTranspose.mulVec w +
        star w ⬝ᵥ (H z).mulVec w).re := by
  have hd := hH.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have ha := quadratic_levi_expansion (H z) (fderiv ℝ H z u)
    (fderiv ℝ H z (Complex.I • u)) (fderiv ℝ (fderiv ℝ H) z u u)
    (fderiv ℝ (fderiv ℝ H) z (Complex.I • u) (Complex.I • u))
    (hermitian_fderiv hd hh u) (hermitian_fderiv hd hh (Complex.I • u)) v w
  unfold leviTrace hermitianQuadratic
  rw [hessian_re (complexQuadratic_C2 hH v),hessian_re (complexQuadratic_C2 hH v)]
  change (fderiv ℝ (fderiv ℝ (complexQuadratic H)) (z,v) (u,w) (u,w)).re +
    (fderiv ℝ (fderiv ℝ (complexQuadratic H)) (z,v)
      (Complex.I • u,Complex.I • w) (Complex.I • u,Complex.I • w)).re = _
  rw [← Complex.add_re,complexQuadratic_hessian hH,complexQuadratic_hessian hH,ha]
  norm_num [Complex.mul_re,wirtingerDerivative,mixedHessian]

lemma hermitianQuadratic_levi_nonneg [DecidableEq ι]
    {H : X → Matrix ι ι ℂ} {z : X} (hH : ContDiffAt ℝ 2 H z)
    (hh : ∀ᶠ y in 𝓝 z, (H y).IsHermitian) (hpos : (H z).PosDef)
    (hcurv : ∀ u : X, (mixedHessian H z u -
      (wirtingerDerivative H z u).conjTranspose*(H z)⁻¹*wirtingerDerivative H z u).PosSemidef)
    (v : ι → ℂ) (u : X) (w : ι → ℂ) :
    0 ≤ leviTrace (hermitianQuadratic H) (z,v) (u,w) := by
  rw [hermitianQuadratic_levi hH hh]
  exact mul_nonneg (by norm_num) (matrix_completed_square_nonneg hpos (hcurv u) v w)

lemma curvature_nonneg_of_strict [DecidableEq ι]
    {H : X → Matrix ι ι ℂ} {z : X}
    (hcurv : ∀ u : X, u ≠ 0 → (mixedHessian H z u -
      (wirtingerDerivative H z u).conjTranspose*(H z)⁻¹*wirtingerDerivative H z u).PosDef)
    (u : X) : (mixedHessian H z u -
      (wirtingerDerivative H z u).conjTranspose*(H z)⁻¹*wirtingerDerivative H z u).PosSemidef := by
  by_cases hu : u=0
  · subst u
    simpa [mixedHessian,wirtingerDerivative] using (Matrix.PosSemidef.zero : (0 : Matrix ι ι ℂ).PosSemidef)
  · exact (hcurv u hu).posSemidef

theorem chern_positive_dual_norm_psh [DecidableEq ι] [CompleteSpace X]
    {Ω : Set X} (hΩ : IsOpen Ω) {H : X → Matrix ι ι ℂ}
    (hH : ContDiffOn ℝ 2 H Ω) (hpos : ∀ z∈Ω, (H z).PosDef)
    (hcurv : ∀ z∈Ω, ∀ u : X, u ≠ 0 → (mixedHessian H z u -
      (wirtingerDerivative H z u).conjTranspose*(H z)⁻¹*wirtingerDerivative H z u).PosDef) :
    DiskPshOn (Ω ×ˢ Set.univ) (hermitianQuadratic H) := by
  apply DiskPshOn.of_C2_leviTrace_nonneg (hΩ.prod isOpen_univ)
  · intro p hp
    exact (hermitianQuadratic_C2 (hH.contDiffAt (hΩ.mem_nhds hp.1)) p.2).contDiffWithinAt
  · rintro ⟨z,v⟩ hz ⟨u,w⟩
    apply hermitianQuadratic_levi_nonneg (hH.contDiffAt (hΩ.mem_nhds hz.1)) _ (hpos z hz.1)
      (curvature_nonneg_of_strict (hcurv z hz.1))
    filter_upwards [hΩ.mem_nhds hz.1] with y hy
    exact (hpos y hy).isHermitian

end
end QuadricCounterexample

end OAI
