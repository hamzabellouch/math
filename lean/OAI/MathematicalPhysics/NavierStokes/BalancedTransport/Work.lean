import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Model

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def pd (i : Fin 3) (f : Space → F) (x : Space) : F :=
  fderiv ℝ f x (Pi.single i 1)

@[simp] theorem pd_const (i : Fin 3) (a : F) (x : Space) :
    pd i (fun _ => a) x = 0 := by simp [pd]

@[simp] theorem pd_coord (i j : Fin 3) (x : Space) :
    pd i (fun y : Space => y j) x = (Pi.single i (1 : ℝ) : Space) j := by
  rw [pd, (hasFDerivAt_apply j x).fderiv]
  rfl

@[simp] theorem pd_sub_const (i : Fin 3) (f : Space → F) (a : F) (x : Space) :
    pd i (fun y => f y - a) x = pd i f x := by
  simp only [pd, fderiv_sub_const]

theorem pd_add (i : Fin 3) {f g : Space → F} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    pd i (fun y => f y + g y) x = pd i f x + pd i g x := by
  simp only [pd, fderiv_fun_add hf hg, add_apply]

theorem pd_sub (i : Fin 3) {f g : Space → F} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    pd i (fun y => f y - g y) x = pd i f x - pd i g x := by
  simp only [pd, fderiv_fun_sub hf hg, sub_apply]

theorem pd_mul (i : Fin 3) {f g : Space → ℝ} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    pd i (fun y => f y * g y) x = f x * pd i g x + g x * pd i f x := by
  simp only [pd, fderiv_fun_mul hf hg, add_apply,
    smul_apply, smul_eq_mul]

theorem pd_apply (i j : Fin 3) {f : Space → Space} {x : Space}
    (hf : DifferentiableAt ℝ f x) :
    pd i (fun y => f y j) x = pd i f x j := by
  simp only [pd, fderiv_apply hf, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]

theorem pd_contDiff (i : Fin 3) {f : Space → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (pd i f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem pd_comm (i j : Fin 3) {f : Space → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Space) :
    pd i (pd j f) x = pd j (pd i f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp) x
  have he (v : Space) : fderiv ℝ (fun y => fderiv ℝ f y v) x =
      (ContinuousLinearMap.apply ℝ F v) ∘L fderiv ℝ (fderiv ℝ f) x :=
    ((ContinuousLinearMap.apply ℝ F v).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) x (Pi.single i 1) =
    fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x (Pi.single j 1)
  simp only [he, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  exact hf.contDiffAt.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)) _ _

def curl (A : Space → Space) (x : Space) : Space :=
  ![pd 1 (fun y => A y 2) x - pd 2 (fun y => A y 1) x,
    pd 2 (fun y => A y 0) x - pd 0 (fun y => A y 2) x,
    pd 0 (fun y => A y 1) x - pd 1 (fun y => A y 0) x]

def divergence (A : Space → Space) (x : Space) : ℝ :=
  ∑ i, pd i (fun y => A y i) x

theorem curl_contDiff {A : Space → Space} (hA : ContDiff ℝ (⊤ : ℕ∞) A) :
    ContDiff ℝ (⊤ : ℕ∞) (curl A) := by
  have he := contDiff_pi.mp hA
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact (pd_contDiff 1 (he 2)).sub (pd_contDiff 2 (he 1))
  · exact (pd_contDiff 2 (he 0)).sub (pd_contDiff 0 (he 2))
  · exact (pd_contDiff 0 (he 1)).sub (pd_contDiff 1 (he 0))

theorem divergence_curl {A : Space → Space} (hA : ContDiff ℝ (⊤ : ℕ∞) A) (x : Space) :
    divergence (curl A) x = 0 := by
  have he := contDiff_pi.mp hA
  have hd (i j : Fin 3) : DifferentiableAt ℝ (pd i (fun y => A y j)) x :=
    (pd_contDiff i (he j)).differentiable (by simp) x
  simp only [divergence, Fin.sum_univ_succ, curl, Matrix.cons_val_zero,
    Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero]
  change (pd 0 (fun y => pd 1 (fun z => A z 2) y - pd 2 (fun z => A z 1) y) x) +
    ((pd 1 (fun y => pd 2 (fun z => A z 0) y - pd 0 (fun z => A z 2) y) x) +
    (pd 2 (fun y => pd 0 (fun z => A z 1) y - pd 1 (fun z => A z 0) y) x)) = 0
  rw [pd_sub _ (hd 1 2) (hd 2 1), pd_sub _ (hd 2 0) (hd 0 2),
    pd_sub _ (hd 0 1) (hd 1 0)]
  rw [pd_comm 0 1 (he 2), pd_comm 0 2 (he 1), pd_comm 1 2 (he 0)]
  ring

theorem curl_congr {A B : Space → Space} {x : Space}
    (h : A =ᶠ[𝓝 x] B) : curl A x = curl B x := by
  have he (j : Fin 3) : (fun y => A y j) =ᶠ[𝓝 x] (fun y => B y j) :=
    h.mono (fun _ hh => congrFun hh j)
  simp only [curl, pd, (he 0).fderiv_eq, (he 1).fderiv_eq, (he 2).fderiv_eq]

@[simp] theorem curl_zero : curl (0 : Space → Space) = 0 := by
  funext x
  simp [curl]

theorem tsupport_curl_subset (A : Space → Space) :
    tsupport (curl A) ⊆ tsupport A := by
  apply closure_minimal _ (isClosed_tsupport A)
  intro x hx
  by_contra hxA
  have hh : A =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxA
  have hz := curl_congr hh
  exact hx (by simpa using hz)

theorem curl_hasCompactSupport {A : Space → Space} (hA : HasCompactSupport A) :
    HasCompactSupport (curl A) :=
  hA.of_isClosed_subset (isClosed_tsupport _) (tsupport_curl_subset A)

def affinePotential (c v l : Space) (x : Space) : Space :=
  ![(1 / 2 : ℝ) * (v 1 * (x 2 - c 2) - v 2 * (x 1 - c 1)) +
      (1 / 3 : ℝ) * (l 1 - l 2) * (x 1 - c 1) * (x 2 - c 2),
    (1 / 2 : ℝ) * (v 2 * (x 0 - c 0) - v 0 * (x 2 - c 2)) +
      (1 / 3 : ℝ) * (l 2 - l 0) * (x 2 - c 2) * (x 0 - c 0),
    (1 / 2 : ℝ) * (v 0 * (x 1 - c 1) - v 1 * (x 0 - c 0)) +
      (1 / 3 : ℝ) * (l 0 - l 1) * (x 0 - c 0) * (x 1 - c 1)]

theorem affinePotential_contDiff (c v l : Space) :
    ContDiff ℝ (⊤ : ℕ∞) (affinePotential c v l) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [affinePotential] <;> fun_prop

theorem curl_affinePotential (c v l : Space) (hl : ∑ i, l i = 0) (x : Space) :
    curl (affinePotential c v l) x = fun i => v i + l i * (x i - c i) := by
  have hl' : l 0 + l 1 + l 2 = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hl
  funext i
  fin_cases i <;>
    simp (disch := fun_prop) [curl, affinePotential, pd_add, pd_sub, pd_mul, Pi.single_apply] <;>
    nlinarith [mul_eq_zero_of_left hl' (x 0 - c 0),
      mul_eq_zero_of_left hl' (x 1 - c 1), mul_eq_zero_of_left hl' (x 2 - c 2)]

def boxCutoff (a b : Space) (η : ℝ) (x : Space) : ℝ :=
  ∏ i : Fin 3, Real.smoothTransition ((x i - a i + 2 * η) / η) *
    Real.smoothTransition ((b i + 2 * η - x i) / η)

def openEnlargement (a b : Space) (η : ℝ) : Set Space :=
  Set.pi Set.univ (fun i => Set.Ioo (a i - η) (b i + η))

def closedEnlargement (a b : Space) (η : ℝ) : Set Space :=
  Set.Icc (fun i => a i - η) (fun i => b i + η)

@[simp] theorem mem_openEnlargement (a b : Space) (η : ℝ) (x : Space) :
    x ∈ openEnlargement a b η ↔ ∀ i, a i - η < x i ∧ x i < b i + η := by
  simp [openEnlargement]

@[simp] theorem mem_closedEnlargement (a b : Space) (η : ℝ) (x : Space) :
    x ∈ closedEnlargement a b η ↔ ∀ i, a i - η ≤ x i ∧ x i ≤ b i + η := by
  simp only [closedEnlargement, mem_Icc, Pi.le_def, forall_and]

theorem openEnlargement_isOpen (a b : Space) (η : ℝ) :
    IsOpen (openEnlargement a b η) := by
  exact isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)

theorem closedEnlargement_isCompact (a b : Space) (η : ℝ) :
    IsCompact (closedEnlargement a b η) := isCompact_Icc

theorem boxCutoff_contDiff (a b : Space) (η : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (boxCutoff a b η) := by
  unfold boxCutoff
  fun_prop

theorem boxCutoff_eq_one {a b : Space} {η : ℝ} (hη : 0 < η) {x : Space}
    (hx : x ∈ closedEnlargement a b η) : boxCutoff a b η x = 1 := by
  apply Finset.prod_eq_one
  intro i _
  obtain ⟨hl, hr⟩ := (mem_closedEnlargement _ _ _ _).mp hx i
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ hη).mpr (by linarith)),
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ hη).mpr (by linarith)), one_mul]

theorem boxCutoff_eventually_one {a b : Space} {η : ℝ} (hη : 0 < η)
    {x : Space} (hx : x ∈ openEnlargement a b η) :
    boxCutoff a b η =ᶠ[𝓝 x] 1 := by
  filter_upwards [(openEnlargement_isOpen a b η).mem_nhds hx] with y hy
  apply boxCutoff_eq_one hη
  exact (mem_closedEnlargement _ _ _ _).mpr fun i =>
    ⟨((mem_openEnlargement _ _ _ _).mp hy i).1.le,
      ((mem_openEnlargement _ _ _ _).mp hy i).2.le⟩

theorem boxCutoff_eq_zero {a b : Space} {η : ℝ} (hη : 0 < η) {x : Space}
    (hx : x ∉ closedEnlargement a b (2 * η)) : boxCutoff a b η x = 0 := by
  rw [mem_closedEnlargement] at hx
  push Not at hx
  obtain ⟨i, hi⟩ := hx
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  by_cases hl : a i - 2 * η ≤ x i
  · have he : Real.smoothTransition ((b i + 2 * η - x i) / η) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
        (by linarith [hi hl]) hη.le)
    rw [he, mul_zero]
  · have he : Real.smoothTransition ((x i - a i + 2 * η) / η) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
        (by linarith) hη.le)
    rw [he, zero_mul]

theorem tsupport_boxCutoff_subset (a b : Space) {η : ℝ} (hη : 0 < η) :
    tsupport (boxCutoff a b η) ⊆ closedEnlargement a b (2 * η) := by
  apply closure_minimal _ (closedEnlargement_isCompact _ _ _).isClosed
  intro x hx
  by_contra hn
  exact hx (boxCutoff_eq_zero hη hn)

theorem boxCutoff_hasCompactSupport (a b : Space) {η : ℝ} (hη : 0 < η) :
    HasCompactSupport (boxCutoff a b η) :=
  (closedEnlargement_isCompact _ _ _).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_boxCutoff_subset a b hη)

def localizedAffine (a b c v l : Space) (η : ℝ) : Space → Space :=
  curl (fun x => boxCutoff a b η x • affinePotential c v l x)

theorem localizedAffine_contDiff (a b c v l : Space) (η : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (localizedAffine a b c v l η) :=
  curl_contDiff ((boxCutoff_contDiff a b η).smul (affinePotential_contDiff c v l))

theorem localizedAffine_divergence (a b c v l : Space) (η : ℝ) (x : Space) :
    divergence (localizedAffine a b c v l η) x = 0 :=
  divergence_curl ((boxCutoff_contDiff a b η).smul (affinePotential_contDiff c v l)) x

theorem localizedAffine_eq {a b c v l : Space} {η : ℝ} (hη : 0 < η)
    (hl : ∑ i, l i = 0) {x : Space} (hx : x ∈ openEnlargement a b η) :
    localizedAffine a b c v l η x = fun i => v i + l i * (x i - c i) := by
  unfold localizedAffine
  rw [curl_congr (show (fun y => boxCutoff a b η y • affinePotential c v l y) =ᶠ[𝓝 x]
      affinePotential c v l from (boxCutoff_eventually_one hη hx).mono
        (fun y hy => by simp only [hy, Pi.one_apply, one_smul])), curl_affinePotential c v l hl]

theorem tsupport_localizedAffine_subset (a b c v l : Space) {η : ℝ} (hη : 0 < η) :
    tsupport (localizedAffine a b c v l η) ⊆ closedEnlargement a b (2 * η) := by
  refine (tsupport_curl_subset _).trans ?_
  apply closure_minimal _ (closedEnlargement_isCompact _ _ _).isClosed
  intro x hx
  by_contra hn
  exact hx (by simp [boxCutoff_eq_zero hη hn])

theorem localizedAffine_hasCompactSupport (a b c v l : Space) {η : ℝ} (hη : 0 < η) :
    HasCompactSupport (localizedAffine a b c v l η) :=
  (closedEnlargement_isCompact _ _ _).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_localizedAffine_subset a b c v l hη)

end BalancedTransport.Geometry
end

end OAI
