import OAI.Algebra.Determinantal.SchurLifts

namespace OAI

namespace PermanentBorder.PolarAnalysis
open Matrix Schur Filter
open scoped Topology
variable {κ J T : Type*} [Fintype κ] [Finite J]
  [NormedAddCommGroup T] [NormedSpace ℂ T]

 theorem finite_simple_polar_kernel_lifts {n : ℕ}
    (i₀ : Fin (n+1)) (F : T → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hF : ∀ i j, ContDiff ℂ 2 (fun y => F y i j))
    (ψ : (ℂ × (κ → ℂ)) → T) (h : κ → T) (x : J → (ℂ × (κ → ℂ)))
    (hψ : ∀ j, DifferentiableAt ℂ ψ (x j))
    (hz : ∀ j, polarPair (fun y => (F y).det) ψ h (x j) = 0)
    (hsimple : ∀ j, (fderiv ℂ (polarPair (fun y => (F y).det) ψ h) (x j)).IsInvertible) :
    ∃ S : Matrix (Fin (n+1)) (Fin (n+1)) ℂ, S.det ≠ 0 ∧ ∀ j, ∃ r : Fin (n+1),
      let F' := fun y => (F y * S).submatrix (pivotEquiv r) (pivotEquiv i₀)
      matrixKernelSystem F' ψ h (matrixKernelPoint F' ψ (x j)) = 0 ∧
        (fderiv ℂ (matrixKernelSystem F' ψ h) (matrixKernelPoint F' ψ (x j))).IsInvertible := by
  have hFd : ∀ y, DifferentiableAt ℂ (fun y i j => F y i j) y := by
    intro y
    apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    exact (hF i j).differentiable (by norm_num) y
  obtain ⟨S,hS,hs⟩ := selected_simple_common_kernel_chart i₀ (fun y i j => F y i j)
    ψ (polarPair (fun y => (F y).det) ψ h) x (fun j => hFd _) hψ
    (fun j => differentiableAt_polarPair (contDiff_det hF).contDiffAt (hψ j))
    (fun _ => rfl) hsimple
  refine ⟨S,hS,?_⟩
  intro j
  obtain ⟨r,hr⟩ := hs j
  refine ⟨r,?_⟩
  let F' := fun y => (F y * S).submatrix (pivotEquiv r) (pivotEquiv i₀)
  change matrixKernelSystem F' ψ h (matrixKernelPoint F' ψ (x j)) = 0 ∧ _
  have hF' : ∀ a b, ContDiff ℂ 2 (fun y => F' y a b) := by
    intro a b
    change ContDiff ℂ 2 (fun y => ∑ k, F y (pivotEquiv r a) k * S k (pivotEquiv i₀ b))
    apply ContDiff.sum
    intro k _
    exact (hF _ _).mul contDiff_const
  obtain ⟨c,hc,hcF⟩ := determinant_pivot_scalar i₀ r
  have hcs : c*S.det ≠ 0 := mul_ne_zero hc hS
  have hdet (y : T) : (F' y).det = (c*S.det)*(F y).det := by
    rw [hcF, Matrix.det_mul]
    ring
  have hrel : (fun y => (F y).det) =ᶠ[𝓝 (ψ (x j))]
      (fun y => (c*S.det)⁻¹ * (F' y).det) := by
    apply Filter.Eventually.of_forall
    intro y
    dsimp only
    rw [hdet, ← mul_assoc, inv_mul_cancel₀ hcs, one_mul]
  obtain ⟨hzero,hsimp⟩ := simple_polarPair_unit contDiffAt_const
    (contDiff_det hF').contDiffAt (hψ j) hrel (inv_ne_zero hcs) (hz j) (hsimple j)
  apply simple_matrix_kernel_lift F' hF' (hψ j)
    (pivot_minor_ne_zero (F (ψ (x j)) * S) i₀ r hr) hzero hsimp
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.KernelBilinear
open MvPolynomial PolarAnalysis PolarAnalysis.Schur
open scoped Classical
variable {κ : Type} [Fintype κ] {n : ℕ}
abbrev ChartSpace (κ : Type) (n : ℕ) := (ℂ × (κ → ℂ)) × ((Fin n → ℂ) × (Fin n → ℂ))
noncomputable def optionProduct : (Option κ → ℂ) ≃L[ℂ] (ℂ × (κ → ℂ)) :=
  (LinearEquiv.piOptionEquivProd ℂ).toContinuousLinearEquiv
@[simp] lemma optionProduct_apply (z : Option κ → ℂ) : optionProduct z = (z none,fun i => z (some i)) := rfl
@[simp] lemma optionProduct_symm_apply (z : ℂ × (κ → ℂ)) (i : Option κ) :
    optionProduct.symm z i = i.elim z.1 z.2 := by cases i <;> rfl

@[simp] lemma pivot_symm (i : Fin (n+1)) : (pivotEquiv i).symm i = .inl () :=
  (pivotEquiv i).symm_apply_apply (.inl ())
@[simp] lemma pivot_symm_succAbove (i : Fin (n+1)) (j : Fin n) :
    (pivotEquiv i).symm (i.succAbove j) = .inr j :=
  (pivotEquiv i).symm_apply_apply (.inr j)

noncomputable def norm (i : Fin (n+1)) (z : Fin n → ℂ) : Fin (n+1) → ℂ :=
  normalized z ∘ (pivotEquiv i).symm
@[simp] lemma norm_pivot (i : Fin (n+1)) (z : Fin n → ℂ) : norm i z i = 1 := by
  change normalized z ((pivotEquiv i).symm (pivotEquiv i (.inl ()))) = 1
  simp [normalized]
@[simp] lemma norm_succAbove (i : Fin (n+1)) (z : Fin n → ℂ) (j : Fin n) :
    norm i z (i.succAbove j) = z j := by
  change normalized z ((pivotEquiv i).symm (pivotEquiv i (.inr j))) = z j
  simp [normalized]

noncomputable def chart (i r : Fin (n+1)) (z : ChartSpace κ n) : Variables κ n → ℂ :=
  coordinates (optionProduct.symm z.1) (norm i z.2.1) (norm r z.2.2)
noncomputable def base (i r : Fin (n+1)) : Groups → Variables κ n
  | none => ⟨none,none⟩
  | some false => ⟨some false,i⟩
  | some true => ⟨some true,r⟩
omit [Fintype κ] in
lemma base_group (i r : Fin (n+1)) (j : Groups) : (base (κ := κ) i r j).1 = j := by
  rcases j with _ | (_ | _) <;> rfl
lemma chart_base (i r : Fin (n+1)) (z : ChartSpace κ n) (j : Groups) :
    chart i r z (base i r j) = 1 := by
  rcases j with _ | (_ | _) <;> simp [chart, coordinates, base]
lemma contDiff_chart (i r : Fin (n+1)) : ContDiff ℂ 1 (chart (κ := κ) i r) := by
  apply contDiff_pi.mpr
  rintro ⟨j,t⟩
  rcases j with _ | (_ | _)
  · rcases t with _ | (_ | t) <;> simp [chart, coordinates] <;> fun_prop
  · change ContDiff ℂ 1 (fun z : ChartSpace κ n => normalized z.2.1 ((pivotEquiv i).symm t))
    cases (pivotEquiv i).symm t <;> simp [normalized] <;> fun_prop
  · change ContDiff ℂ 1 (fun z : ChartSpace κ n => normalized z.2.2 ((pivotEquiv r).symm t))
    cases (pivotEquiv r).symm t <;> simp [normalized] <;> fun_prop

noncomputable def outputLinear (r : Fin (n+1)) : (Equations κ n → ℂ) ≃ₗ[ℂ] ChartSpace κ n where
  toFun y := ((y (.inl r), fun k => y (.inr (.inr k))),
    (fun j => y (.inl (r.succAbove j)), fun j => y (.inr (.inl j))))
  invFun z := Sum.elim
    (fun i => ((pivotEquiv r).symm i).elim (fun _ => z.1.1) z.2.1)
    (Sum.elim z.2.2 z.1.2)
  left_inv y := by
    funext i
    rcases i with i | j | k
    · obtain ⟨a,rfl⟩ := (pivotEquiv r).surjective i
      rcases a with u | a
      · cases u; simp
      · simp
    · rfl
    · rfl
  right_inv z := by
    apply Prod.ext
    · apply Prod.ext
      · change ((pivotEquiv r).symm (pivotEquiv r (.inl ()))).elim _ _ = _
        simp
      · rfl
    · apply Prod.ext
      · funext j
        change ((pivotEquiv r).symm (pivotEquiv r (.inr j))).elim _ _ = _
        simp
      · rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
noncomputable def output (r : Fin (n+1)) : (Equations κ n → ℂ) ≃L[ℂ] ChartSpace κ n :=
  (outputLinear r).toContinuousLinearEquiv

lemma chart_separated {i r s : Fin (n+1)} {x y : ChartSpace κ n} (h : x.1 ≠ y.1) :
    Multigraded.BlockSeparated Sigma.fst (chart i r x) (chart i s y) := by
  have he : optionProduct.symm x.1 ≠ optionProduct.symm y.1 :=
    fun e => h (optionProduct.symm.injective e)
  obtain ⟨j,hj⟩ := Function.ne_iff.mp he
  refine ⟨⟨none,none⟩,⟨none,some j⟩,rfl,?_⟩
  simpa [chart, coordinates] using hj.symm
end PermanentBorder.KernelBilinear

namespace PermanentBorder.KernelBilinear
open MvPolynomial Matrix PolarAnalysis PolarAnalysis.Schur
open scoped Classical
variable {κ : Type} [Fintype κ] {n : ℕ}

lemma sum_norm (i : Fin (n+1)) (f : Fin (n+1) → ℂ) (z : Fin n → ℂ) :
    ∑ j, f j * norm i z j = f i + ∑ j, f (i.succAbove j) * z j := by
  rw [Fin.sum_univ_succAbove _ i]
  simp

lemma polar_norm (i r : Fin (n+1)) (B : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (u v : Fin n → ℂ) :
    (∑ a, ∑ b, B a b * norm i u b * norm r v a) =
      normalized v ⬝ᵥ ((B.submatrix (pivotEquiv r) (pivotEquiv i)) *ᵥ normalized u) := by
  simp only [mulVec, dotProduct]
  symm
  apply Fintype.sum_equiv (pivotEquiv r)
  intro a
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv (pivotEquiv i) _ _ (fun b => by
    simp [norm, Matrix.submatrix_apply, mul_comm, mul_left_comm])

section Bridge
variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]

lemma system_eq_matrixKernelSystem
    (F : T → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (ψ : (ℂ × (κ → ℂ)) → T) (h : κ → T)
    (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (B : κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hlocal : ∀ z i j, A₀ i j + ∑ k, A k i j * optionProduct.symm z k = F (ψ z) i j)
    (hdir : ∀ y k i j, fderiv ℂ (fun y => F y i j) y (h k) = B k i j)
    (i r : Fin (n+1)) (z : ChartSpace κ n) :
    output r (fun j => eval (chart i r z) (system A₀ A B i j)) =
      matrixKernelSystem (fun y => (F y).submatrix (pivotEquiv r) (pivotEquiv i)) ψ h z := by
  have hright (a : Fin (n+1)) :
      eval (chart i r z) (rightEquation A₀ A a) =
        F (ψ z.1) a i + ∑ j, F (ψ z.1) a (i.succAbove j) * z.2.1 j := by
    change eval (coordinates _ _ _) _ = _
    rw [eval_right]
    simp only [hlocal]
    exact sum_norm i _ _
  have hleft (b : Fin (n+1)) :
      eval (chart i r z) (leftEquation A₀ A b) =
        F (ψ z.1) r b + ∑ a, z.2.2 a * F (ψ z.1) (r.succAbove a) b := by
    change eval (coordinates _ _ _) _ = _
    rw [eval_left]
    simp only [hlocal]
    rw [sum_norm]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    exact mul_comm _ _
  have hpolar (k : κ) :
      eval (chart i r z) (polarEquation (B k)) =
        normalized z.2.2 ⬝ᵥ ((B k).submatrix (pivotEquiv r) (pivotEquiv i) *ᵥ normalized z.2.1) := by
    change eval (coordinates _ _ _) _ = _
    rw [eval_polar, polar_norm]
  have hdir' (k : κ) :
      dirMatrix (fun y => (F y).submatrix (pivotEquiv r) (pivotEquiv i))
        (ψ z.1) (h k) = (B k).submatrix (pivotEquiv r) (pivotEquiv i) := by
    ext a b
    exact hdir _ _ _ _
  apply Prod.ext
  · apply Prod.ext
    · change eval (chart i r z) (rightEquation A₀ A r) = _
      rw [hright]
      rfl
    · funext k
      change eval (chart i r z) (polarEquation (B k)) = _
      rw [hpolar]
      change _ = normalized z.2.2 ⬝ᵥ (dirMatrix
        (fun y => block ((F y).submatrix (pivotEquiv r) (pivotEquiv i) (.inl ()) (.inl ()))
          (fun j => (F y).submatrix (pivotEquiv r) (pivotEquiv i) (.inl ()) (.inr j))
          (fun j => (F y).submatrix (pivotEquiv r) (pivotEquiv i) (.inr j) (.inl ()))
          (((F y).submatrix (pivotEquiv r) (pivotEquiv i)).submatrix Sum.inr Sum.inr))
        (ψ z.1) (h k) *ᵥ normalized z.2.1)
      have hb : (fun y => block ((F y).submatrix (pivotEquiv r) (pivotEquiv i) (.inl ()) (.inl ()))
          (fun j => (F y).submatrix (pivotEquiv r) (pivotEquiv i) (.inl ()) (.inr j))
          (fun j => (F y).submatrix (pivotEquiv r) (pivotEquiv i) (.inr j) (.inl ()))
          (((F y).submatrix (pivotEquiv r) (pivotEquiv i)).submatrix Sum.inr Sum.inr)) =
          (fun y => (F y).submatrix (pivotEquiv r) (pivotEquiv i)) := by
        funext y a b
        cases a with
        | inl u => cases u; cases b with
          | inl v => cases v; rfl
          | inr b => rfl
        | inr a => cases b with
          | inl v => cases v; rfl
          | inr b => rfl
      rw [hb, hdir']
  · apply Prod.ext
    · funext j
      change eval (chart i r z) (rightEquation A₀ A (r.succAbove j)) = _
      rw [hright]
      rfl
    · funext j
      change eval (chart i r z) (leftEquation A₀ A (i.succAbove j)) = _
      rw [hleft]
      rfl
end Bridge
end PermanentBorder.KernelBilinear

namespace PermanentBorder.KernelBilinear
open MvPolynomial Matrix PolarAnalysis PolarAnalysis.Schur
open scoped Classical
variable {κ J : Type} [Fintype κ] [Fintype J] {n : ℕ}
variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]

theorem selected_kernel_count
    (F : T → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (ψ : (ℂ × (κ → ℂ)) → T) (h : κ → T)
    (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (B : κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hlocal : ∀ z i j, A₀ i j + ∑ k, A k i j * optionProduct.symm z k = F (ψ z) i j)
    (hdir : ∀ y k i j, fderiv ℂ (fun y => F y i j) y (h k) = B k i j)
    (i : Fin (n+1)) (r : J → Fin (n+1)) (x : J → ChartSpace κ n)
    (hx : Function.Injective (fun j => (x j).1))
    (hz : ∀ j, matrixKernelSystem
      (fun y => (F y).submatrix (pivotEquiv (r j)) (pivotEquiv i)) ψ h (x j) = 0)
    (hs : ∀ j, (fderiv ℂ (matrixKernelSystem
      (fun y => (F y).submatrix (pivotEquiv (r j)) (pivotEquiv i)) ψ h) (x j)).IsInvertible) :
    Fintype.card J ≤ 2^Fintype.card κ * (2*n+1).choose (Fintype.card κ+1) := by
  classical
  have he (j : J) :
      (fun z => output (r j) (fun a => eval (chart i (r j) z) (system A₀ A B i a))) =
      matrixKernelSystem (fun y => (F y).submatrix (pivotEquiv (r j)) (pivotEquiv i)) ψ h := by
    funext z
    exact system_eq_matrixKernelSystem F ψ h A₀ A B hlocal hdir i (r j) z
  have hz' (j : J) (a : Equations κ n) : eval (chart i (r j) (x j)) (system A₀ A B i a) = 0 := by
    have hh : output (r j) (fun a => eval (chart i (r j) (x j)) (system A₀ A B i a)) =
        output (r j) 0 := by
      rw [map_zero, congrFun (he j) (x j)]
      exact hz j
    exact congrFun ((output (r j)).injective hh) a
  have hc := Multigraded.bilinear_simple_point_count_reindex (dimensions κ n)
    Sigma.fst variablesEquiv variablesEquiv_group firstGroup secondGroup card_equations
    (system A₀ A B i) (system_homogeneous A₀ A B i)
    (fun j => base i (r j)) (fun j => base_group i (r j))
    (fun j => output (r j)) (fun j => chart i (r j)) (fun j => contDiff_chart i (r j))
    (fun j z => chart_base i (r j) z) x
    (fun j k hjk => chart_separated (fun hh => hjk (hx hh))) hz'
    (fun j => by rw [he]; exact hs j)
  exact hc.trans mixed_coefficient_bound
end PermanentBorder.KernelBilinear

namespace PermanentBorder.KernelBilinear
open MvPolynomial Matrix PolarAnalysis PolarAnalysis.Schur
open scoped Classical
variable {σ κ J : Type} [Fintype σ] [Fintype κ] [Fintype J] {n : ℕ}

noncomputable def affine (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : σ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (y : σ → ℂ) :=
  A₀ + ∑ v, y v • A v

lemma affine_contDiff (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : σ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (i j : Fin (n+1)) :
    ContDiff ℂ 2 (fun y => affine A₀ A y i j) := by
  unfold affine
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  fun_prop

lemma affine_derivative (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : σ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (y h : σ → ℂ) (i j : Fin (n+1)) :
    fderiv ℂ (fun y => affine A₀ A y i j) y h = ∑ v, h v * A v i j := by
  let L : (σ → ℂ) →L[ℂ] ℂ := ∑ v, A v i j • ContinuousLinearMap.proj v
  have he : (fun y => affine A₀ A y i j) = (fun y => A₀ i j + L y) := by
    funext y
    simp [affine,L,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,mul_comm]
  have hd : HasFDerivAt (fun y => A₀ i j + L y) L y := by
    exact HasFDerivAt.const_add (A₀ i j) L.hasFDerivAt
  rw [he, hd.fderiv]
  simp [L,mul_comm]

lemma affine_right_mul (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : σ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (S : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (y : σ → ℂ) :
    affine (A₀*S) (fun v => A v*S) y = affine A₀ A y * S := by
  simp [affine, add_mul, Finset.sum_mul]

theorem affine_polar_count
    (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : σ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (b : σ → ℂ) (L : (Option κ → ℂ) →L[ℂ] (σ → ℂ)) (h : κ → σ → ℂ)
    (x : J → ℂ × (κ → ℂ)) (hx : Function.Injective x)
    (hz : ∀ j, polarPair (fun y => (affine A₀ A y).det)
      (fun z => b + L (optionProduct.symm z)) h (x j) = 0)
    (hs : ∀ j, (fderiv ℂ (polarPair (fun y => (affine A₀ A y).det)
      (fun z => b + L (optionProduct.symm z)) h) (x j)).IsInvertible) :
    Fintype.card J ≤ 2^Fintype.card κ * (2*n+1).choose (Fintype.card κ+1) := by
  classical
  let ψ := fun z : ℂ × (κ → ℂ) => b + L (optionProduct.symm z)
  obtain ⟨S,hS,hr⟩ := finite_simple_polar_kernel_lifts (0 : Fin (n+1))
    (affine A₀ A) (affine_contDiff A₀ A) ψ h x
    (fun _ => ((differentiable_const b).add (L.differentiable.comp optionProduct.symm.differentiable)).differentiableAt)
    hz hs
  choose r hr using hr
  let A₀' := A₀*S
  let A' := fun v => A v*S
  let B₀ := affine A₀' A' b
  let B := fun k => ∑ v, L (Pi.single k 1) v • A' v
  let D := fun k => ∑ v, h k v • A' v
  have hlocal (z : ℂ × (κ → ℂ)) (i j : Fin (n+1)) :
      B₀ i j + ∑ k, B k i j * optionProduct.symm z k = affine A₀' A' (ψ z) i j := by
    have hexp : optionProduct.symm z = ∑ k, optionProduct.symm z k • Pi.single k 1 := by
      ext k
      simp [Pi.single_apply]
    have hLe (v : σ) : L (optionProduct.symm z) v =
        ∑ k, optionProduct.symm z k * L (Pi.single k 1) v := by
      conv_lhs => rw [hexp, map_sum]
      simp
    simp only [B₀, B, affine, ψ, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, Pi.add_apply, hLe, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    rw [Finset.sum_comm, ← add_assoc]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hd (y : σ → ℂ) (k : κ) (i j : Fin (n+1)) :
      fderiv ℂ (fun y => affine A₀' A' y i j) y (h k) = D k i j := by
    rw [affine_derivative]
    simp [D,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  let X := fun j => matrixKernelPoint
    (fun y => (affine A₀' A' y).submatrix (pivotEquiv (r j)) (pivotEquiv (0 : Fin (n+1)))) ψ (x j)
  apply selected_kernel_count (affine A₀' A') ψ h B₀ B D hlocal hd 0 r X
  · exact hx
  · intro j
    simpa only [X, A₀', A', affine_right_mul] using (hr j).1
  · intro j
    simpa only [X, A₀', A', affine_right_mul] using (hr j).2
end PermanentBorder.KernelBilinear

end OAI
