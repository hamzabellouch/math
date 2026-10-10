import OAI.Analysis.PeriodicLattice.Certificates

namespace OAI

/-! Uniform certificates for all field derivative words. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingFieldCertificates {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace Quantitative
open RapidCalculus Profiles TorusCalculus RecursiveArithmetic
open scoped ContDiff

section FieldWords
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

def coordD (i : Option (Fin 3)) (F : Field A) : Field A :=
  match i with
  | none => fullTimeD F
  | some j => spaceD j F

def fieldWord (w : List (Option (Fin 3))) (F : Field A) : Field A := w.foldr coordD F

@[simp] theorem fieldWord_nil (F : Field A) : fieldWord [] F = F := rfl
@[simp] theorem fieldWord_cons (i : Option (Fin 3)) (w : List (Option (Fin 3))) (F : Field A) :
    fieldWord (i::w) F = coordD i (fieldWord w F) := rfl

theorem fieldWord_append (w v : List (Option (Fin 3))) (F : Field A) :
    fieldWord (w++v) F = fieldWord w (fieldWord v F) := List.foldr_append

theorem coordD_contDiff {F : Field A} (hF : ContDiff ℝ ∞ (lifted F)) (i : Option (Fin 3)) :
    ContDiff ℝ ∞ (lifted (coordD i F)) := by
  cases i with
  | none => exact contDiff_fullTimeD hF
  | some j => exact contDiff_spaceD hF j

theorem fieldWord_contDiff {F : Field A} (hF : ContDiff ℝ ∞ (lifted F)) (w : List (Option (Fin 3))) :
    ContDiff ℝ ∞ (lifted (fieldWord w F)) := by
  induction w with
  | nil => exact hF
  | cons i w ih => exact coordD_contDiff ih i

theorem coordD_add {F G : Field A} (hF : ContDiff ℝ ∞ (lifted F))
    (hG : ContDiff ℝ ∞ (lifted G)) (i : Option (Fin 3)) :
    coordD i (F+G) = coordD i F + coordD i G := by
  funext t q
  cases i with
  | none =>
    exact deriv_add (fullTime_hasDerivAt hF t q).differentiableAt
      (fullTime_hasDerivAt hG t q).differentiableAt
  | some j => exact spaceD_add (smooth_slice_differentiable hF t) (smooth_slice_differentiable hG t) j q

theorem fieldWord_add {F G : Field A} (hF : ContDiff ℝ ∞ (lifted F))
    (hG : ContDiff ℝ ∞ (lifted G)) (w : List (Option (Fin 3))) :
    fieldWord w (F+G) = fieldWord w F + fieldWord w G := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [fieldWord_cons, ih, coordD_add (fieldWord_contDiff hF w) (fieldWord_contDiff hG w)]; rfl

theorem coordD_scale {F : Field A} (hF : ContDiff ℝ ∞ (lifted F)) (c : ℝ) (i : Option (Fin 3)) :
    coordD i (c • F) = c • coordD i F := by
  cases i with
  | none => exact funext (fun t => funext (fun q => ((fullTime_hasDerivAt hF t q).const_smul c).deriv))
  | some j => exact spaceD_scale hF c j

theorem fieldWord_scale {F : Field A} (hF : ContDiff ℝ ∞ (lifted F)) (c : ℝ)
    (w : List (Option (Fin 3))) : fieldWord w (c • F) = c • fieldWord w F := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [fieldWord_cons, ih, coordD_scale (fieldWord_contDiff hF w) c]; rfl

theorem coordD_zero (i : Option (Fin 3)) : coordD i (0 : Field A) = 0 := by
  funext t q; cases i <;> exact deriv_const _ _

@[simp] theorem fieldWord_zero (w : List (Option (Fin 3))) : fieldWord w (0 : Field A) = 0 := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [fieldWord_cons, ih, coordD_zero]

structure FieldCertificate (F : Input → Field A) where
  budget : Input × ℕ × ℕ → ℕ
  recursive : Primrec budget
  smooth : ∀ d, ContDiff ℝ ∞ (lifted (F d))
  estimate : ∀ d, d.WellFormed → ∀ w n J, w.length ≤ n → ∀ t, 0 ≤ t → ∀ q,
    (1+t)^J * ‖fieldWord w (F d) t q‖ ≤ (budget (d,n,J) : ℝ)

namespace FieldCertificate
noncomputable def diff {F : Input → Field A} (h : FieldCertificate F) (i : Option (Fin 3)) :
    FieldCertificate (fun d => coordD i (F d)) where
  budget p := h.budget (p.1,p.2.1+1,p.2.2)
  recursive := h.recursive.comp (by fun_prop)
  smooth d := coordD_contDiff (h.smooth d) i
  estimate d hd w n J hn t ht q := by
    simpa only [fieldWord_append, fieldWord_cons, fieldWord_nil] using
      h.estimate d hd (w++[i]) (n+1) J (by simpa using Nat.add_le_add_right hn 1) t ht q

noncomputable def add {F G : Input → Field A} (h : FieldCertificate F) (k : FieldCertificate G) :
    FieldCertificate (fun d => F d + G d) where
  budget p := h.budget p + k.budget p
  recursive := Primrec.nat_add.comp h.recursive k.recursive
  smooth d := (h.smooth d).add (k.smooth d)
  estimate d hd w n J hn t ht q := by
    rw [fieldWord_add (h.smooth d) (k.smooth d)]
    calc
      _ ≤ (1+t)^J * (‖fieldWord w (F d) t q‖ + ‖fieldWord w (G d) t q‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ ≤ _ := by rw [mul_add, Nat.cast_add]; exact add_le_add (h.estimate d hd w n J hn t ht q) (k.estimate d hd w n J hn t ht q)

noncomputable def scale {F : Input → Field A} (h : FieldCertificate F) (c : ℝ) (N : ℕ)
    (hc : ‖c‖ ≤ N) : FieldCertificate (fun d => c • F d) where
  budget p := N * h.budget p
  recursive := Primrec.nat_mul.comp (Primrec.const N) h.recursive
  smooth d := (h.smooth d).const_smul c
  estimate d hd w n J hn t ht q := by
    rw [fieldWord_scale (h.smooth d) c, Pi.smul_apply, Pi.smul_apply, norm_smul, mul_left_comm]
    simpa only [Nat.cast_mul] using mul_le_mul hc (h.estimate d hd w n J hn t ht q)
      (by positivity) (Nat.cast_nonneg N)

noncomputable def neg {F : Input → Field A} (h : FieldCertificate F) :
    FieldCertificate (fun d => -F d) := by
  simpa only [neg_one_smul] using h.scale (-1) 1 (by norm_num)
noncomputable def sub {F G : Input → Field A} (h : FieldCertificate F) (k : FieldCertificate G) :
    FieldCertificate (fun d => F d - G d) := by simpa only [sub_eq_add_neg] using h.add k.neg

noncomputable def zero : FieldCertificate (fun _ => (0 : Field A)) where
  budget _ := 0
  recursive := Primrec.const _
  smooth _ := contDiff_const
  estimate d hd w n J hn t ht q := by simp
end FieldCertificate
end FieldWords

theorem coordD_mul {F G : ScalarField} (hF : ContDiff ℝ ∞ (lifted F))
    (hG : ContDiff ℝ ∞ (lifted G)) (i : Option (Fin 3)) :
    coordD i (F*G) = coordD i F * G + F * coordD i G := by
  funext t q
  cases i with
  | none =>
    exact deriv_mul (fullTime_hasDerivAt hF t q).differentiableAt
      (fullTime_hasDerivAt hG t q).differentiableAt
  | some j => exact spaceD_smul hF hG j t q

theorem fieldWord_mul_estimate {F G : ScalarField}
    (hF : ContDiff ℝ ∞ (lifted F)) (hG : ContDiff ℝ ∞ (lifted G))
    (w : List (Option (Fin 3))) (t : ℝ) (q : Torus) (a C D : ℝ) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hf : ∀ v : List (Option (Fin 3)), v.length ≤ w.length → a * ‖fieldWord v F t q‖ ≤ C)
    (hg : ∀ v : List (Option (Fin 3)), v.length ≤ w.length → ‖fieldWord v G t q‖ ≤ D) :
    a * ‖fieldWord w (F*G) t q‖ ≤ 2^w.length * C * D := by
  induction w using List.reverseRecOn generalizing F G with
  | nil =>
    simpa only [fieldWord_nil, Pi.mul_apply, norm_mul, List.length_nil, pow_zero, one_mul,
      ← mul_assoc] using mul_le_mul (hf [] le_rfl) (hg [] le_rfl) (norm_nonneg _) hC
  | append_singleton w i ih =>
    have hfi v (hv : v.length ≤ w.length) : a * ‖fieldWord v (coordD i F) t q‖ ≤ C := by
      simpa only [fieldWord_append, fieldWord_cons, fieldWord_nil] using
        hf (v++[i]) (by simpa only [List.length_append, List.length_singleton] using Nat.add_le_add_right hv 1)
    have hgi v (hv : v.length ≤ w.length) : ‖fieldWord v (coordD i G) t q‖ ≤ D := by
      simpa only [fieldWord_append, fieldWord_cons, fieldWord_nil] using
        hg (v++[i]) (by simpa only [List.length_append, List.length_singleton] using Nat.add_le_add_right hv 1)
    have hf' v (hv : v.length ≤ w.length) := hf v (hv.trans (by simp))
    have hg' v (hv : v.length ≤ w.length) := hg v (hv.trans (by simp))
    have H1 := ih (coordD_contDiff hF i) hG hfi hg'
    have H2 := ih hF (coordD_contDiff hG i) hf' hgi
    rw [fieldWord_append, fieldWord_cons, fieldWord_nil, coordD_mul hF hG,
      fieldWord_add (F := coordD i F * G) (G := F * coordD i G)
        ((coordD_contDiff hF i).mul hG) (hF.mul (coordD_contDiff hG i))]
    calc
      _ ≤ a * (‖fieldWord w (coordD i F * G) t q‖ + ‖fieldWord w (F * coordD i G) t q‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) ha
      _ ≤ 2^w.length*C*D + 2^w.length*C*D := by rw [mul_add]; exact add_le_add H1 H2
      _ = _ := by simp only [List.length_append, List.length_singleton, pow_succ]; ring

namespace FieldCertificate
noncomputable def mul {F G : Input → ScalarField} (h : FieldCertificate F) (k : FieldCertificate G) :
    FieldCertificate (fun d => F d * G d) where
  budget p := 2^p.2.1 * h.budget p * k.budget (p.1,p.2.1,0)
  recursive := by
    have hp : Primrec (fun p : Input × ℕ × ℕ => k.budget (p.1,p.2.1,0)) := k.recursive.comp (by fun_prop)
    exact Primrec.nat_mul.comp (Primrec.nat_mul.comp (by fun_prop) h.recursive) hp
  smooth d := (h.smooth d).mul (k.smooth d)
  estimate d hd w n J hn t ht q := by
    have hh := fieldWord_mul_estimate (h.smooth d) (k.smooth d) w t q ((1+t)^J)
      (h.budget (d,n,J)) (k.budget (d,n,0)) (by positivity) (by positivity)
      (fun v hv => h.estimate d hd v n J (hv.trans hn) t ht q)
      (fun v hv => by simpa using k.estimate d hd v n 0 (hv.trans hn) t ht q)
    refine hh.trans ?_
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    gcongr
    norm_num
end FieldCertificate

theorem fieldWord_tensor_estimate {F : ScalarField} {f : ℝ → ℝ → ℝ} {h : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (hh : ContDiff ℝ ∞ h)
    (he : ∀ t x, F t (torusMk x) = h (x 2) * f t (x 1))
    (w : List (Option (Fin 3))) (t : ℝ) (x : Space) (a C D : ℝ)
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfB : ∀ v : List Bool, v.length ≤ w.length → a * ‖wordD v f t (x 1)‖ ≤ C)
    (hhB : ∀ k : ℕ, k ≤ w.length → ‖iteratedDeriv k h (x 2)‖ ≤ D) :
    a * ‖fieldWord w F t (torusMk x)‖ ≤ D * C := by
  induction w using List.reverseRecOn generalizing F f h with
  | nil =>
    rw [fieldWord_nil, he, norm_mul, mul_left_comm]
    exact mul_le_mul (hhB 0 le_rfl) (hfB [] le_rfl) (by positivity) hD
  | append_singleton w i ih =>
    rw [fieldWord_append, fieldWord_cons, fieldWord_nil]
    have hf' v (hv : v.length ≤ w.length) := hfB v (hv.trans (by simp))
    have hh' k (hk : k ≤ w.length) := hhB k (hk.trans (by simp))
    have hfi (j : Bool) v (hv : v.length ≤ w.length) : a * ‖wordD v (biD j f) t (x 1)‖ ≤ C := by
      simpa only [wordD_append, wordD_cons, wordD_nil] using
        hfB (v++[j]) (by simpa only [List.length_append, List.length_singleton] using Nat.add_le_add_right hv 1)
    cases i with
    | none => exact ih (partial_contDiff hf true) hh (tensor_fullTimeD hf he) (hfi true) hh'
    | some i =>
      fin_cases i
      · change a * ‖fieldWord w (spaceD 0 F) t (torusMk x)‖ ≤ D*C
        rw [tensor_spaceD_zero he]
        simp only [fieldWord_zero, Pi.zero_apply, norm_zero, mul_zero]
        exact mul_nonneg hD hC
      · exact ih (partial_contDiff hf false) hh (tensor_spaceD_one hf he) (hfi false) hh'
      · have hhder : ContDiff ℝ ∞ (deriv h) := by simpa using ContDiff.iterate_deriv 1 hh
        exact ih hf hhder (tensor_spaceD_two hh he) hf'
          (fun k hk => by
            simpa only [← iteratedDeriv_succ'] using
              hhB (k+1) (by simpa only [List.length_append, List.length_singleton] using Nat.add_le_add_right hk 1))

namespace FieldCertificate
noncomputable def tensor {F : Input → ScalarField} {f : Input → ℝ → ℝ → ℝ} {h : ℝ → ℝ}
    (hf : BiCertificate f) (hh : ProfileCertificate h)
    (he : ∀ d t x, F d t (torusMk x) = h (x 2) * f d t (x 1)) : FieldCertificate F where
  budget p := hh.budget p.2.1 * hf.budget p
  recursive := Primrec.nat_mul.comp (hh.recursive.comp (by fun_prop)) hf.recursive
  smooth d := tensor_contDiff (hf.smooth d) hh.smooth (he d)
  estimate d hd w n J hn t ht q := by
    obtain ⟨x,rfl⟩ := mk_surjective q
    simpa only [Nat.cast_mul] using fieldWord_tensor_estimate (hf.smooth d) hh.smooth (he d)
      w t x ((1+t)^J) (hf.budget (d,n,J)) (hh.budget n) (by positivity) (by positivity) (by positivity)
      (fun v hv => hf.estimate d hd v n J (hv.trans hn) t ht (x 1))
      (fun k hk => hh.estimate k n (hk.trans hn) (x 2))
end FieldCertificate

theorem coordD_component {F : VectorField} (hF : ContDiff ℝ ∞ (lifted F))
    (i : Option (Fin 3)) (j : Fin 3) :
    coordD i (fun t q => F t q j) = fun t q => coordD i F t q j := by
  funext t q
  cases i with
  | none =>
    exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).hasFDerivAt.comp_hasDerivAt t
      (fullTime_hasDerivAt hF t q)).deriv
  | some i => exact spaceD_component (smooth_slice_differentiable hF t) i j q

theorem fieldWord_component {F : VectorField} (hF : ContDiff ℝ ∞ (lifted F))
    (w : List (Option (Fin 3))) (j : Fin 3) :
    fieldWord w (fun t q => F t q j) = fun t q => fieldWord w F t q j := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [fieldWord_cons, ih, coordD_component (fieldWord_contDiff hF w) i]; rfl

namespace FieldCertificate
noncomputable def components {F : Input → VectorField}
    (h : ∀ i : Fin 3, FieldCertificate (fun d t q => F d t q i)) : FieldCertificate F where
  budget p := (h 0).budget p + (h 1).budget p + (h 2).budget p
  recursive := Primrec.nat_add.comp (Primrec.nat_add.comp (h 0).recursive (h 1).recursive) (h 2).recursive
  smooth d := contDiff_euclidean.mpr (fun i => (h i).smooth d)
  estimate d hd w n J hn t ht q := by
    have hs : ContDiff ℝ ∞ (lifted (F d)) := contDiff_euclidean.mpr (fun i => (h i).smooth d)
    have H (i : Fin 3) := (h i).estimate d hd w n J hn t ht q
    simp_rw [fieldWord_component hs] at H
    calc
      _ ≤ (1+t)^J * ∑ i : Fin 3, ‖fieldWord w (F d) t q i‖ :=
        mul_le_mul_of_nonneg_left (norm_le_sum_components _) (by positivity)
      _ ≤ _ := by
        rw [Fin.sum_univ_three, mul_add, mul_add, Nat.cast_add, Nat.cast_add]
        exact add_le_add (add_le_add (H 0) (H 1)) (H 2)
noncomputable def component {F : Input → VectorField} (h : FieldCertificate F) (i : Fin 3) :
    FieldCertificate (fun d t q => F d t q i) where
  budget := h.budget
  recursive := h.recursive
  smooth d := (contDiff_euclidean.mp (h.smooth d)) i
  estimate d hd w n J hn t ht q := by
    rw [fieldWord_component (h.smooth d)]
    exact (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le (fieldWord w (F d) t q) i) (by positivity)).trans
      (h.estimate d hd w n J hn t ht q)

noncomputable def diffusion {F : Input → VectorField} (h : FieldCertificate F) :
    FieldCertificate (fun d => laplacian (F d)) := by
  have he : (fun d => laplacian (F d)) = fun d =>
    spaceD 0 (spaceD 0 (F d)) + spaceD 1 (spaceD 1 (F d)) + spaceD 2 (spaceD 2 (F d)) := by
    funext d t q; exact Fin.sum_univ_three _
  rw [he]
  exact ((h.diff (some 0)).diff (some 0)).add ((h.diff (some 1)).diff (some 1)) |>.add
    ((h.diff (some 2)).diff (some 2))

noncomputable def transport {F : Input → VectorField} (h : FieldCertificate F) :
    FieldCertificate (fun d => advection (F d)) := by
  apply components
  intro j
  have he : (fun d t q => advection (F d) t q j) = fun d =>
      (fun t q => F d t q 0 * spaceD 0 (F d) t q j) +
      (fun t q => F d t q 1 * spaceD 1 (F d) t q j) +
      (fun t q => F d t q 2 * spaceD 2 (F d) t q j) := by
    funext d t q
    simp only [advection, Fin.sum_univ_three, PiLp.add_apply, PiLp.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [he]
  exact ((h.component 0).mul ((h.diff (some 0)).component j)).add
    ((h.component 1).mul ((h.diff (some 1)).component j)) |>.add
    ((h.component 2).mul ((h.diff (some 2)).component j))

noncomputable def gradient {F : Input → ScalarField} (h : FieldCertificate F) :
    FieldCertificate (fun d => PeriodicLattice.gradient (F d)) :=
  components (fun i => h.diff (some i))

noncomputable def residual {F : Input → VectorField} (h : FieldCertificate F) (ν : ℝ) (N : ℕ)
    (hν : ‖ν‖ ≤ N) : FieldCertificate (fun d => Residual.fullForce ν (F d)) :=
  ((h.diff none).add h.transport).sub (h.diffusion.scale ν N hν)
end FieldCertificate

noncomputable def velocityCertificate : FieldCertificate FluidLift.velocity := by
  apply FieldCertificate.components
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => i.elim0)))
  · exact FieldCertificate.tensor aCertificate slopeCertificate (fun d t x => by simp)
  · exact FieldCertificate.tensor bCertificate slopeCertificate (fun d t x => by simp)
  · exact FieldCertificate.tensor (bCertificate.diff false) etaCertificate.neg (fun d t x => by simp [FluidLift.bdy, biD])

noncomputable def potentialCertificate : FieldCertificate FluidLift.potential :=
  (FieldCertificate.tensor pressureBaseCertificate ProfileCertificate.one
    (fun d t x => by simp [PeriodicInverse.horizontal, torusMk, Function.Periodic.lift_coe])).add
  (FieldCertificate.tensor pressureModeCertificate doubleSlopeCertificate FluidLift.pressureOsc_cover)

noncomputable def forceCertificate (ν : ℝ) (N : ℕ) (hν : ‖ν‖ ≤ N) : FieldCertificate (FluidLift.force ν) :=
  velocityCertificate.residual ν N hν

noncomputable def solenoidalForceCertificate (ν : ℝ) (N : ℕ) (hν : ‖ν‖ ≤ N) :
    FieldCertificate (FluidLift.solenoidalForce ν) :=
  (forceCertificate ν N hν).sub potentialCertificate.gradient

section MixedWords
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

theorem fieldWord_replicate (i : Option (Fin 3)) (n : ℕ) (F : Field A) :
    fieldWord (List.replicate n i) F = (coordD i)^[n] F := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, fieldWord_cons, Function.iterate_succ_apply', ih]

def spatialWord (α : MultiIndex) : List (Option (Fin 3)) :=
  List.replicate (α 2) (some 2) ++ List.replicate (α 1) (some 1) ++ List.replicate (α 0) (some 0)
def mixedWord (r : ℕ) (α : MultiIndex) : List (Option (Fin 3)) :=
  List.replicate r none ++ spatialWord α

theorem mixedD_eq_fieldWord {F : Field A} (hF : ContDiff ℝ ∞ (lifted F))
    (r : ℕ) (α : MultiIndex) {t : ℝ} (ht : 0 ≤ t) (q : Torus) :
    mixedD r α F t q = fieldWord (mixedWord r α) F t q := by
  have hh := fieldWord_contDiff hF (spatialWord α)
  simp only [spatialWord, fieldWord_append, fieldWord_replicate] at hh
  simp only [mixedD, mixedWord, spatialWord, fieldWord_append, fieldWord_replicate]
  exact iterate_timeD_eq_fullTimeD hh r t ht q
end MixedWords

def mixedOrder (r : ℕ) (α : MultiIndex) : ℕ := r + (α 2 + α 1 + α 0)

@[fun_prop] theorem mixedOrder_recursive : Primrec (fun p : ℕ × MultiIndex => mixedOrder p.1 p.2) := by
  have hi (i : Fin 3) : Primrec (fun p : ℕ × MultiIndex => p.2 i) :=
    Primrec.fin_app.comp Primrec.snd (Primrec.const i)
  exact Primrec.nat_add.comp Primrec.fst (Primrec.nat_add.comp (Primrec.nat_add.comp (hi 2) (hi 1)) (hi 0))

namespace FieldCertificate
noncomputable def mixedBudget {F : Input → VectorField} (h : FieldCertificate F)
    (d : Input) (r : ℕ) (α : MultiIndex) (J : ℕ) : ℕ := h.budget (d,mixedOrder r α,J)

theorem mixedBudget_recursive {F : Input → VectorField} (h : FieldCertificate F) :
    Primrec (fun p : Input × ℕ × MultiIndex × ℕ => h.mixedBudget p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold mixedBudget
  exact h.recursive.comp (by fun_prop)

theorem mixed_estimate {F : Input → VectorField} (h : FieldCertificate F) (d : Input) (hd : d.WellFormed)
    (r : ℕ) (α : MultiIndex) (J : ℕ) {t : ℝ} (ht : 0 ≤ t) (q : Torus) :
    (1+t)^J * ‖mixedD r α (F d) t q‖ ≤ (h.mixedBudget d r α J : ℝ) := by
  rw [mixedD_eq_fieldWord (h.smooth d) r α ht]
  exact h.estimate d hd (mixedWord r α) (mixedOrder r α) J
    (by simp [mixedWord, spatialWord, mixedOrder, Nat.add_assoc]) t ht q

theorem sup_estimate {F : Input → VectorField} (h : FieldCertificate F) (d : Input) (hd : d.WellFormed)
    (r : ℕ) (α : MultiIndex) (J : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    spatialSup (mixedD r α (F d)) t ≤ (h.mixedBudget d r α J : ℝ) / (1+t)^J := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨q,rfl⟩
  exact (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using h.mixed_estimate d hd r α J ht q)
end FieldCertificate
end Quantitative

end
end PeriodicLattice

end OAI
