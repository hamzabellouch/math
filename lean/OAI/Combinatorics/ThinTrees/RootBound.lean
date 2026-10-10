import OAI.Combinatorics.ThinTrees.RankOne

namespace OAI

universe uI uD uR uS

section

noncomputable section
open Polynomial Finset Matrix
open scoped MatrixOrder ComplexOrder
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {R : Type uR} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D]

def pencil [CommRing R] (A : I → Matrix D D R) : MvPolynomial I R :=
  Matrix.det (fun a b => ∑i, MvPolynomial.X i*MvPolynomial.C (A i a b))

omit [DecidableEq I] in
lemma pencil_eval [CommRing R] (A : I → Matrix D D R) (z : I → R) :
    MvPolynomial.eval z (pencil A)=(∑i, z i • A i).det := by
  let M : Matrix D D (MvPolynomial I R) := fun a b => ∑i, MvPolynomial.X i*MvPolynomial.C (A i a b)
  change (MvPolynomial.eval z) M.det = _
  rw [(MvPolynomial.eval z).map_det M]
  congr 1
  ext a b
  change (MvPolynomial.eval z) (∑i, MvPolynomial.X i*MvPolynomial.C (A i a b)) = _
  simp [Matrix.sum_apply,Matrix.smul_apply]

omit [DecidableEq I] in
lemma pencil_map {S : Type uS} [CommRing R] [CommRing S] (f : R →+* S) (A : I → Matrix D D R) :
    (pencil A).map f=pencil (fun i => (A i).map f) := by
  let M : Matrix D D (MvPolynomial I R) := fun a b => ∑i, MvPolynomial.X i*MvPolynomial.C (A i a b)
  change (MvPolynomial.map f) M.det = _
  rw [(MvPolynomial.map f).map_det M]
  unfold pencil
  congr 1
  apply Matrix.ext
  intro a b
  change (MvPolynomial.map f) (∑i, MvPolynomial.X i*MvPolynomial.C (A i a b)) = _
  simp [Matrix.map_apply]

lemma posSemidef_complex {A : Matrix D D ℝ} (hA : A.PosSemidef) :
    (A.map (algebraMap ℝ ℂ)).PosSemidef := by
  let S := CFC.sqrt A
  have hS : S.IsHermitian := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have he : Sᴴ*S=A := by rw [hS.eq]; exact CFC.sqrt_mul_sqrt_self A hA.nonneg
  rw [←he]
  have hm : (Sᴴ*S).map (algebraMap ℝ ℂ)=(S.map (algebraMap ℝ ℂ))ᴴ*S.map (algebraMap ℝ ℂ) := by
    rw [Matrix.map_mul]
    congr 1
    ext i j
    simp
  rw [hm]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [DecidableEq I] in
lemma real_pencil_stable (A : I → Matrix D D ℝ) (hA : ∀i, (A i).PosSemidef)
    (hsum : ∑i, A i=1) : RealStable (pencil A) := by
  unfold RealStable
  rw [pencil_map]
  apply determinantPencil_stable _ (fun i => posSemidef_complex (hA i))
  have he : ∑i, (A i).map (algebraMap ℝ ℂ)=(1 : Matrix D D ℂ) := by
    ext a b
    simp only [Matrix.sum_apply,Matrix.map_apply]
    rw [←map_sum]
    rw [←Matrix.sum_apply,hsum]
    simp [Matrix.one_apply]
  rw [he]
  exact Matrix.PosDef.one

omit [DecidableEq I] in
lemma pencil_above (A : I → Matrix D D ℝ) (hA : ∀i, (A i).PosSemidef)
    (hsum : ∑i, A i=1) {t : ℝ} (ht : 0 < t) : Above (pencil A) (fun _ => t) := by
  intro s hs
  rw [pencil_eval]
  have he : ∑i, ((fun _ : I => t)+s) i • A i=t • (1 : Matrix D D ℝ)+∑i,s i • A i := by
    simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib,←Finset.smul_sum,hsum]
  rw [he]
  exact ((Matrix.PosDef.one.smul ht).add_posSemidef
    (Matrix.posSemidef_sum _ (fun i _ => (hA i).smul (hs i)))).det_pos

omit [Fintype D] [DecidableEq D] in
lemma sum_update_smul [CommRing R] (A : I → Matrix D D R) (z : I → R) (j : I) (u : R) :
    ∑i, (Function.update z j (z j+u)) i • A i=(∑i, z i • A i)+u • A j := by
  classical
  have he : Function.update z j (z j+u)=z+Pi.single j u := by
    ext i
    by_cases hi : i=j
    · subst i; simp
    · simp [Function.update_of_ne hi,Pi.single_eq_of_ne hi]
  rw [he]
  simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi; simp [Pi.single_eq_of_ne hi]
  · simp

lemma ray_pencil_constant (A : I → Matrix D D ℝ) (hsum : ∑i, A i=1) (j : I) (t : ℝ) :
    ray (pencil A) (fun _ => t) j=((C t : ℝ[X]) • (1 : Matrix D D ℝ[X])+(X : ℝ[X]) • (A j).map C).det := by
  apply Polynomial.funext
  intro u
  rw [ray_eval,pencil_eval,sum_update_smul,←Finset.smul_sum,hsum]
  rw [show Polynomial.eval u = Polynomial.evalRingHom u from rfl, (Polynomial.evalRingHom u).map_det]
  congr 1
  ext a b
  simp [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,apply_ite]
  ring

lemma ray_pencil_factor (A : I → Matrix D D ℝ) (hsum : ∑i, A i=1) (j : I) {t : ℝ} (ht : t ≠ 0) :
    ray (pencil A) (fun _ => t) j=C (t^(Fintype.card D)) * (1+(X : ℝ[X]) • ((t⁻¹) • A j).map C).det := by
  rw [ray_pencil_constant A hsum]
  have he : (C t : ℝ[X]) • (1 : Matrix D D ℝ[X])+(X : ℝ[X]) • (A j).map C=
      (C t : ℝ[X]) • (1+(X : ℝ[X]) • ((t⁻¹) • A j).map C) := by
    ext a b
    simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.map_apply,smul_eq_mul,map_mul]
    rw [mul_add]
    congr 1
    rw [←mul_assoc,←mul_assoc,mul_comm (C t) X,mul_assoc X,←map_mul,mul_inv_cancel₀ ht,map_one,mul_one]
  rw [he,Matrix.det_smul,map_pow]

lemma pencil_barrier (A : I → Matrix D D ℝ) (hsum : ∑i, A i=1) (j : I) {t : ℝ} (ht : t ≠ 0) :
    barrier (pencil A) (fun _ => t) j=(A j).trace/t := by
  have hnum : MvPolynomial.eval (fun _ => t) (MvPolynomial.pderiv j (pencil A))=
      t^(Fintype.card D)*((t⁻¹) • A j).trace := by
    rw [←ray_zero,←ray_derivative,ray_pencil_factor A hsum j ht,Polynomial.derivative_mul]
    simp only [Polynomial.derivative_C,zero_mul,zero_add,Polynomial.eval_mul,Polynomial.eval_C,
      Matrix.derivative_det_one_add_X_smul]
  have hden : MvPolynomial.eval (fun _ => t) (pencil A)=t^(Fintype.card D) := by
    rw [pencil_eval,←Finset.smul_sum,hsum,Matrix.det_smul,Matrix.det_one,mul_one]
  rw [barrier,hnum,hden,Matrix.trace_smul]
  simp only [smul_eq_mul]
  field_simp

def realDifferentialProduct (dirs : List I) (p : MvPolynomial I ℝ) : MvPolynomial I ℝ :=
  dirs.foldl (fun q j => q-MvPolynomial.pderiv j q) p

def shiftVector (dirs : List I) (δ : ℝ) : I → ℝ :=
  (dirs.map (fun j => Pi.single j δ)).sum

omit [Fintype I] in
lemma shiftVector_cons (j : I) (dirs : List I) (δ : ℝ) :
    shiftVector (j::dirs) δ=Pi.single j δ+shiftVector dirs δ := by
  simp [shiftVector]

lemma many_barrier_shifts {p : MvPolynomial I ℝ} (hp : RealStable p) {z : I → ℝ}
    (hz : Above p z) {δ φ : ℝ} (hδ : 0 < δ) (hφ : φ+1/δ ≤ 1)
    (hb : ∀i, barrier p z i ≤ φ) (dirs : List I) :
    Above (realDifferentialProduct dirs p) (z+shiftVector dirs δ) ∧
      ∀i, barrier (realDifferentialProduct dirs p) (z+shiftVector dirs δ) i ≤ φ := by
  induction dirs generalizing p z with
  | nil => simpa [realDifferentialProduct,shiftVector] using And.intro hz hb
  | cons j dirs ih =>
    obtain ⟨hw,hb'⟩ := barrier_shift hp hz j hδ (by linarith [hb j])
    have hh := ih (hp.sub_pderiv j) hw (fun i => (hb' i).trans (hb i))
    simpa only [realDifferentialProduct,List.foldl_cons,shiftVector_cons,update_add_single,add_assoc] using hh

lemma shiftVector_univ (δ : ℝ) : shiftVector (Finset.univ.toList : List I) δ=fun _ => δ := by
  ext i
  simp [shiftVector,Finset.sum_apply,Pi.single_apply]

lemma skew_root_bound (A : I → Matrix D D ℝ) (hA : ∀i, (A i).PosSemidef)
    (hsum : ∑i, A i=1) {ε : ℝ} (hε : 0 < ε) (htr : ∀i, (A i).trace ≤ ε) :
    Above (realDifferentialProduct Finset.univ.toList (pencil A)) (fun _ => (1+Real.sqrt ε)^2) := by
  let t := ε+Real.sqrt ε
  let δ := 1+Real.sqrt ε
  have ht : 0 < t := add_pos_of_pos_of_nonneg hε (Real.sqrt_nonneg _)
  have hδ : 0 < δ := add_pos_of_pos_of_nonneg zero_lt_one (Real.sqrt_nonneg _)
  have hid : ε/t+1/δ=1 := by
    have hsq := Real.sq_sqrt hε.le
    dsimp [t,δ] at *
    field_simp
    nlinarith
  have hb : ∀i, barrier (pencil A) (fun _ => t) i ≤ ε/t := by
    intro i
    rw [pencil_barrier A hsum i ht.ne']
    exact div_le_div_of_nonneg_right (htr i) ht.le
  have hh := (many_barrier_shifts (real_pencil_stable A hA hsum) (pencil_above A hA hsum ht)
    hδ hid.le hb (Finset.univ.toList : List I)).1
  rw [shiftVector_univ] at hh
  have he : (fun _ : I => t)+(fun _ => δ)=fun _ => (1+Real.sqrt ε)^2 := by
    ext i
    simp only [Pi.add_apply]
    dsimp [t,δ]
    nlinarith [Real.sq_sqrt hε.le]
  rwa [he] at hh

end StrongThinTree.MSS

end
end

end OAI
