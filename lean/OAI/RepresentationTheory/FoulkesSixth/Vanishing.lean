import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.VanishingSteps

namespace OAI

noncomputable section

namespace Foulkes.Vanishing
open MvPolynomial Foulkes.Polarization Foulkes.PolynomialSpan

def extendPerm {r : ℕ} (σ : Equiv.Perm (Fin r)) : Equiv.Perm (Fin (r+1)) where
  toFun := Fin.lastCases (Fin.last r) (fun i => (σ i).castSucc)
  invFun := Fin.lastCases (Fin.last r) (fun i => (σ.symm i).castSucc)
  left_inv := by intro i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv := by intro i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

@[simp] lemma extendPerm_castSucc {r : ℕ} (σ : Equiv.Perm (Fin r)) (i : Fin r) :
    extendPerm σ i.castSucc = (σ i).castSucc := by simp [extendPerm]

@[simp] lemma extendPerm_last {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    extendPerm σ (Fin.last r) = Fin.last r := by simp [extendPerm]

def embedRows {r n : ℕ} : P r n →ₐ[ℂ] P (r+1) n :=
  rename (fun ij : Fin r × Fin n => (ij.1.castSucc,ij.2))

lemma embedRows_rowLift {r n : ℕ} (i : Fin r) (p : S n) :
    embedRows (rowLift i p) = rowLift i.castSucc p := by
  simp [embedRows, rowLift, rename_rename, Function.comp_def]

@[simp] lemma embedRows_rowForm {r n : ℕ} (i : Fin r) (v : Fin n → ℂ) :
    embedRows (rowForm i v) = rowForm i.castSucc v := by simp [embedRows, rowForm]

lemma embedRows_pureRows {r n b : ℕ} (v : Fin r → Fin n → ℂ) :
    embedRows (pureRows b v) = ∏ i, rowForm i.castSucc (v i) ^ b := by
  simp only [pureRows, map_prod, map_pow, embedRows_rowForm]

lemma embedRows_tensorRows {r n : ℕ} (p : Fin r → S n) :
    embedRows (tensorRows p) = ∏ i, rowLift i.castSucc (p i) := by
  simp only [tensorRows, map_prod, embedRows_rowLift]

lemma renameRow_embedRows {r n : ℕ} (σ : Equiv.Perm (Fin r)) (f : P r n) :
    renameRow (extendPerm σ) (embedRows f) = embedRows (renameRow σ f) := by
  simp [renameRow, embedRows, rename_rename, Function.comp_def]

lemma renameRow_commonPower {r n : ℕ} (σ : Equiv.Perm (Fin r)) (x : Fin n → ℂ) :
    renameRow (extendPerm σ) (commonPower x) = commonPower x := by
  simp only [commonPower, map_prod, map_pow, renameRow_rowForm, extendPerm_castSucc]
  exact Equiv.prod_comp σ (fun i => rowForm i.castSucc x ^ r)

def restrictionFunctional {r n : ℕ} (l : P (r+1) n →ₗ[ℂ] ℂ)
    (x t : Fin n → ℂ) (b : ℕ) : P r n →ₗ[ℂ] ℂ :=
  (l.comp (LinearMap.mulLeft ℂ (commonPower x * rowForm (Fin.last r) t ^ b))).comp embedRows.toLinearMap

@[simp] lemma restrictionFunctional_apply {r n : ℕ} (l : P (r+1) n →ₗ[ℂ] ℂ)
    (x t : Fin n → ℂ) (b : ℕ) (f : P r n) :
    restrictionFunctional l x t b f =
      l ((commonPower x * rowForm (Fin.last r) t ^ b) * embedRows f) := rfl

lemma restriction_symmetric {r n b : ℕ} {l : P (r+1) n →ₗ[ℂ] ℂ}
    (hs : Symmetric l) (x t : Fin n → ℂ) : Symmetric (restrictionFunctional l x t b) := by
  intro σ f
  simp only [restrictionFunctional_apply, ← renameRow_embedRows]
  have hh := hs (extendPerm σ) ((commonPower x * rowForm (Fin.last r) t ^ b) * embedRows f)
  simpa only [map_mul, map_pow, renameRow_commonPower, renameRow_rowForm, extendPerm_last] using hh

lemma restriction_products {r m n : ℕ} (hr : 0 < r) {l : P (r+1) n →ₗ[ℂ] ℂ}
    (hs : Symmetric l) (hz : ProductsVanish l (r+m)) (x t : Fin n → ℂ) :
    ProductsVanish (restrictionFunctional l x t (r+m)) m := by
  intro y
  rw [← tensorRows_diag_product, restrictionFunctional_apply, embedRows_tensorRows]
  have hh := free_last_slot hr hs hz x t y
  simp only [map_mul, map_pow, rowLift_lin, Finset.prod_mul_distrib] at hh
  simpa only [commonPower, mul_assoc, mul_left_comm, mul_comm] using hh

lemma eval_cast_rowLinear {r n : ℕ} (u : Fin (r+1)) (i : Fin r)
    (w : Fin (r+1) × Fin n → ℂ) :
    eval (fun ij => algebraMap ℂ (P (r+1) n) (w ij))
      (GenericShift.rowLinear u (fun k => (X (i.castSucc,k) : P (r+1) n))) =
      rowForm i.castSucc (fun k => w (u,k)) :=
  GenericShift.eval_rowLinear u _ w

lemma eval_induction_family_univ {r n j : ℕ} (w : Fin (r+1) × Fin n → ℂ) :
    eval (fun ij => algebraMap ℂ (P (r+1) n) (w ij))
      (GenericShift.family (fun i : Fin r => fun k => (X (i.castSucc,k) : P (r+1) n))
        j r Finset.univ) =
      commonPower (fun k => w (Fin.last r,k)) *
        embedRows (pureRows (j-r) (fun i k => w (i.castSucc,k))) := by
  simp only [GenericShift.family, GenericShift.mixedProduct, Finset.mem_univ, ite_true,
    map_prod, map_mul, map_pow, eval_cast_rowLinear, embedRows_pureRows, commonPower]
  exact Finset.prod_mul_distrib

lemma eval_induction_family_empty {r n j : ℕ} (w : Fin (r+1) × Fin n → ℂ) :
    eval (fun ij => algebraMap ℂ (P (r+1) n) (w ij))
      (GenericShift.family (fun i : Fin r => fun k => (X (i.castSucc,k) : P (r+1) n))
        j r ∅) = embedRows (pureRows j (fun i k => w (i.castSucc,k))) := by
  simp only [GenericShift.family, GenericShift.mixedProduct, Finset.notMem_empty, ite_false,
    map_prod, map_pow, eval_cast_rowLinear, embedRows_pureRows]

lemma remove_common_power {r m n : ℕ} (hb : r*r ≤ r+m)
    {l : P (r+1) n →ₗ[ℂ] ℂ} (t : Fin n → ℂ)
    (hz : ∀ (x : Fin n → ℂ) (f : P r n), f ∈ W r n m →
      restrictionFunctional l x t (r+m) f = 0)
    (v : Fin r → Fin n → ℂ) :
    l ((∏ i : Fin r, rowForm i.castSucc (v i) ^ (r+m)) *
      rowForm (Fin.last r) t ^ (r+m)) = 0 := by
  let c := fun i : Fin r => fun k : Fin n => (X (i.castSucc,k) : P (r+1) n)
  let lt : P (r+1) n →ₗ[ℂ] ℂ :=
    l.comp (LinearMap.mulLeft ℂ (rowForm (Fin.last r) t ^ (r+m)))
  have hfull : mapCoeffs lt (GenericShift.family c (r+m) r Finset.univ) = 0 := by
    apply MvPolynomial.funext
    intro w
    rw [eval_mapCoeffs, eval_induction_family_univ, Nat.add_sub_cancel_left, map_zero]
    have hh := hz (fun k => w (Fin.last r,k))
      (pureRows m (fun i k => w (i.castSucc,k))) (pureRows_mem _)
    change l ((commonPower (fun k => w (Fin.last r,k)) * rowForm (Fin.last r) t ^ (r+m)) *
      embedRows (pureRows m (fun i k => w (i.castSucc,k)))) = 0 at hh
    change l (rowForm (Fin.last r) t ^ (r+m) * (commonPower (fun k => w (Fin.last r,k)) *
      embedRows (pureRows m (fun i k => w (i.castSucc,k))))) = 0
    rw [← mul_assoc, mul_comm (rowForm (Fin.last r) t ^ (r+m))]
    exact hh
  have hzero := family_zero_of_all_shifted c lt hb hfull
  let w : Fin (r+1) × Fin n → ℂ := fun ij => Fin.lastCases 0 (fun i => v i ij.2) ij.1
  have hh := congrArg (eval w) hzero
  rw [eval_mapCoeffs, eval_induction_family_empty, map_zero] at hh
  change l (rowForm (Fin.last r) t ^ (r+m) * embedRows (pureRows (r+m) _)) = 0 at hh
  rw [embedRows_pureRows, mul_comm] at hh
  simpa only [w, Fin.lastCases_castSucc] using hh

theorem vanishing (a : ℕ) : ∀ {n b : ℕ}, 1 ≤ a → 1 ≤ b → a*(a-1) ≤ b →
    ∀ {l : P a n →ₗ[ℂ] ℂ}, Symmetric l → ProductsVanish l b →
      ∀ f : P a n, f ∈ W a n b → l f = 0 := by
  induction a with
  | zero => intro n b ha; omega
  | succ r ih =>
    intro n b ha hb0 hb l hs hz f hf
    have hpure : ∀ v : Fin (r+1) → Fin n → ℂ, l (pureRows b v) = 0 := by
      intro v
      by_cases hr : r = 0
      · subst r
        have hh := hz (fun _ => v 0)
        simpa [pureRows, z, Fin.prod_univ_one] using hh
      · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
        have hrb : r ≤ b := by
          simp only [Nat.add_sub_cancel] at hb
          nlinarith
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hrb
        have hm : r*r ≤ m := by
          simp only [Nat.add_sub_cancel] at hb
          nlinarith
        have hrestrict (x t : Fin n → ℂ) (g : P r n) (hg : g ∈ W r n m) :
            restrictionFunctional l x t (r+m) g = 0 := by
          apply ih (by omega) (by nlinarith) ?_ (restriction_symmetric hs x t)
            (restriction_products hrpos hs hz x t) g hg
          have hpred : r-1 ≤ r := Nat.sub_le _ _
          exact (Nat.mul_le_mul_left r hpred).trans hm
        have hh := remove_common_power (by nlinarith : r*r ≤ r+m)
          (v (Fin.last r)) (fun x g hg => hrestrict x (v (Fin.last r)) g hg)
          (fun i => v i.castSucc)
        simpa only [pureRows, Fin.prod_univ_castSucc] using hh
    have hW : W (r+1) n b ≤ LinearMap.ker l := by
      rw [W_eq_span_pureRows]
      apply Submodule.span_le.mpr
      rintro _ ⟨v,rfl⟩
      exact hpure v
    exact hW hf

end Foulkes.Vanishing

namespace Foulkes.Vanishing
open MvPolynomial Foulkes.Polarization

lemma average_renameRow {a n : ℕ} (τ : Equiv.Perm (Fin a)) (f : P a n) :
    average a n (renameRow τ f) = average a n f := by
  simp only [average_apply, renameRow_comp]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight τ) (fun σ => renameRow σ f)

theorem quadratic_bound (a n b : ℕ) (ha : 1 ≤ a) (hb0 : 1 ≤ b) (hb : a*(a-1) ≤ b) :
    R a n b = W a n b ⊓ (A a n).toSubmodule := by
  classical
  apply le_antisymm
  · intro f hf
    refine ⟨hf.1, ?_⟩
    by_contra hnot
    obtain ⟨l, hlf, hlA⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
    have hkill (p : P a n) (hp : p ∈ A a n) : l p = 0 := by
      have hh : l p ∈ (A a n).toSubmodule.map l := Submodule.mem_map.mpr ⟨p,hp,rfl⟩
      rwa [hlA, Submodule.mem_bot] at hh
    let lav := l.comp (average a n)
    have hs : Symmetric lav := by
      intro σ p
      change l (average a n (renameRow σ p)) = l (average a n p)
      rw [average_renameRow]
    have hz : ProductsVanish lav b := by
      intro y
      have hp : (∏ j : Fin b, z (y j)) ∈ A a n :=
        (A a n).prod_mem (fun j _ => z_mem_A (y j))
      change l (average a n (∏ j, z (y j))) = 0
      rw [average_eq (A_le_rowInvariants a n hp)]
      exact hkill _ hp
    have hh := vanishing a ha hb0 hb hs hz f hf.1
    change l (average a n f) = 0 at hh
    rw [average_eq hf.2] at hh
    exact hlf hh
  · exact AComponent_le_R a n b

theorem sixth_quadratic_bound (n b : ℕ) (hb : 30 ≤ b) :
    R 6 n b = W 6 n b ⊓ (A 6 n).toSubmodule :=
  quadratic_bound 6 n b (by omega) (by omega) (by omega)

end Foulkes.Vanishing

end

end OAI
