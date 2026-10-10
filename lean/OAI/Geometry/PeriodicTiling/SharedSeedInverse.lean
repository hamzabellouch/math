import OAI.Geometry.PeriodicTiling.SharedSeedLabelEquiv

namespace OAI

universe uK uΔ uA uB uR

noncomputable section

namespace PeriodicTilingThree.SharedSeed

variable {K : Type uK} {Δ : Type uΔ} {A : Type uA} {B : Type uB} {R : Type uR}
  [AddCommGroup K] [AddCommGroup R] {m b n : ℕ}

def sourceResidueEquiv (sx : R) (e : R ≃ LabelledResidue m) : R ≃ LabelledResidue m where
  toFun τ := e (sx - τ)
  invFun s := sx - e.symm s
  left_inv τ := by simp
  right_inv s := by simp

@[simp] theorem sourceResidueEquiv_apply (sx : R) (e : R ≃ LabelledResidue m) (τ : R) :
    sourceResidueEquiv sx e τ = e (sx - τ) := rfl

@[simp] theorem sourceResidueEquiv_symm_apply (sx : R) (e : R ≃ LabelledResidue m)
    (s : LabelledResidue m) : (sourceResidueEquiv sx e).symm s = sx - e.symm s := rfl

def usefulOne (D : LabeledBlocks K A B 2 b) (u : K) : LabelledResidue m → ZMod 2 × ZMod b
  | Sum.inl _ => D.C u
  | Sum.inr (Sum.inl (_, y)) => (y, 0)
  | Sum.inr (Sum.inr (_, y, _)) => (y, 0)

def highOne (D : LabeledBlocks K A B 2 b) (t : ℤ) (u : K) : LabelledResidue m → K
  | Sum.inl _ => D.T t u
  | Sum.inr _ => u

def usefulTwo (D : LabeledBlocks K A B 3 b) (u : K) : LabelledResidue m → ZMod 3 × ZMod b
  | Sum.inl y => (y, 0)
  | Sum.inr (Sum.inl _) => D.C u
  | Sum.inr (Sum.inr (_, _, y)) => (y, 0)

def highTwo (D : LabeledBlocks K A B 3 b) (t : ℤ) (u : K) : LabelledResidue m → K
  | Sum.inl _ => u
  | Sum.inr (Sum.inl _) => D.T t u
  | Sum.inr (Sum.inr _) => u

def oneForward (D : LabeledBlocks K A B 2 b) (S : BlockShiftData Δ 2 b)
    (e : R ≃ LabelledResidue m) (code : R ≃ ZMod n)
    (H : (K × Δ) × R → ℤ) (x : ℤ) (sx : R) (k : K)
    (v : (K × Δ) × R) : ((ZMod 2 × ZMod b) × K) × ZMod n :=
  let s := e (sx - v.2)
  let u := k - v.1.1
  let t := x - H v
  ((usefulOne D u s + S.e v.1.2, highOne D t u s),
    sharedOutput e code t (sx - v.2))

def twoForward (D : LabeledBlocks K A B 3 b) (S : BlockShiftData Δ 3 b)
    (e : R ≃ LabelledResidue m) (code : R ≃ ZMod n)
    (H : (K × Δ) × R → ℤ) (x : ℤ) (sx : R) (k : K)
    (v : (K × Δ) × R) : ((ZMod 3 × ZMod b) × K) × ZMod n :=
  let s := e (sx - v.2)
  let u := k - v.1.1
  let t := x - H v
  ((usefulTwo D u s + S.e v.1.2, highTwo D t u s),
    sharedOutput e code t (sx - v.2))

def oneActivationEquiv (D : LabeledBlocks K A B 2 b) (S : BlockShiftData Δ 2 b)
    (e : R ≃ LabelledResidue m) (code : R ≃ ZMod n)
    (H : (K × Δ) × R → ℤ)
    (hA : ∀ v, (H v : ZMod 2) = S.rhoA v.1.2)
    (hB : ∀ v, (H v : ZMod b) = S.rhoB v.1.2)
    (x : ℤ) (sx : R) (k : K) :
    ((K × Δ) × R) ≃ (((ZMod 2 × ZMod b) × K) × ZMod n) :=
  let E := sourceResidueEquiv sx e
  let blocks := fun y : ZMod 3 =>
    BlockShiftData.blockInverseEquiv D S (fun v => H (v, E.symm (Sum.inl y)))
      (fun v => hA (v, E.symm (Sum.inl y)))
      (fun v => hB (v, E.symm (Sum.inl y))) x k
  ((Equiv.prodCongr (Equiv.refl (K × Δ)) E).trans
    (oneLabelEquiv S x k blocks)).trans
      (Equiv.prodCongr (Equiv.refl ((ZMod 2 × ZMod b) × K)) (e.symm.trans code))

def twoActivationEquiv (D : LabeledBlocks K A B 3 b) (S : BlockShiftData Δ 3 b)
    (e : R ≃ LabelledResidue m) (code : R ≃ ZMod n)
    (H : (K × Δ) × R → ℤ)
    (hA : ∀ v, (H v : ZMod 3) = S.rhoA v.1.2)
    (hB : ∀ v, (H v : ZMod b) = S.rhoB v.1.2)
    (x : ℤ) (sx : R) (k : K) :
    ((K × Δ) × R) ≃ (((ZMod 3 × ZMod b) × K) × ZMod n) :=
  let E := sourceResidueEquiv sx e
  let blocks := fun y : Fin 2 × ZMod 2 =>
    BlockShiftData.blockInverseEquiv D S (fun v => H (v, E.symm (Sum.inr (Sum.inl y))))
      (fun v => hA (v, E.symm (Sum.inr (Sum.inl y))))
      (fun v => hB (v, E.symm (Sum.inr (Sum.inl y)))) x k
  ((Equiv.prodCongr (Equiv.refl (K × Δ)) E).trans
    (twoLabelEquiv S x k blocks)).trans
      (Equiv.prodCongr (Equiv.refl ((ZMod 3 × ZMod b) × K)) (e.symm.trans code))

theorem oneActivationEquiv_apply
    (D : LabeledBlocks K A B 2 b) (S : BlockShiftData Δ 2 b)
    (e : R ≃ LabelledResidue m) (code : R ≃ ZMod n)
    (H : (K × Δ) × R → ℤ)
    (hA : ∀ v, (H v : ZMod 2) = S.rhoA v.1.2)
    (hB : ∀ v, (H v : ZMod b) = S.rhoB v.1.2)
    (hOther : ∀ v, (H v : ZMod 3) = 0)
    (x : ℤ) (sx : R) (k : K) (v : (K × Δ) × R) :
    oneActivationEquiv D S e code H hA hB x sx k v =
      oneForward D S e code H x sx k v := by
  rcases v with ⟨⟨l, δ⟩, τ⟩
  have hback : sx - e.symm (e (sx - τ)) = τ := by simp
  cases hs : e (sx - τ) with
  | inl y =>
      rw [hs] at hback
      simp [oneActivationEquiv, oneLabelEquiv, sourceResidueEquiv,
        BlockShiftData.blockInverseEquiv, BlockShiftData.blockForward,
        oneForward, usefulOne, highOne, sharedOutput, rotation, rotate, rotateMap,
        hs, hback, Int.cast_sub, hOther]
  | inr s =>
      cases s with
      | inl cy =>
          rcases cy with ⟨c, y⟩
          simp [oneActivationEquiv, oneLabelEquiv, sourceResidueEquiv,
            inactiveEquiv, inactiveForward, oneForward, usefulOne, highOne,
            sharedOutput, rotation, rotate, rotateMap, hs, Int.cast_sub, hA,
            add_sub_assoc, Prod.add_def]
      | inr cyz =>
          rcases cyz with ⟨c, y, z⟩
          simp [oneActivationEquiv, oneLabelEquiv, sourceResidueEquiv,
            inactiveEquiv, inactiveForward, oneForward, usefulOne, highOne,
            sharedOutput, rotation, rotate, rotateMap, hs, Int.cast_sub, hA, hOther,
            add_sub_assoc, Prod.add_def]

theorem twoActivationEquiv_apply
    (D : LabeledBlocks K A B 3 b) (S : BlockShiftData Δ 3 b)
    (e : R ≃ LabelledResidue m) (code : R ≃ ZMod n)
    (H : (K × Δ) × R → ℤ)
    (hA : ∀ v, (H v : ZMod 3) = S.rhoA v.1.2)
    (hB : ∀ v, (H v : ZMod b) = S.rhoB v.1.2)
    (hOther : ∀ v, (H v : ZMod 2) = 0)
    (x : ℤ) (sx : R) (k : K) (v : (K × Δ) × R) :
    twoActivationEquiv D S e code H hA hB x sx k v =
      twoForward D S e code H x sx k v := by
  rcases v with ⟨⟨l, δ⟩, τ⟩
  have hback : sx - e.symm (e (sx - τ)) = τ := by simp
  cases hs : e (sx - τ) with
  | inl y =>
      simp [twoActivationEquiv, twoLabelEquiv, sourceResidueEquiv,
        inactiveEquiv, inactiveForward, twoForward, usefulTwo, highTwo,
        sharedOutput, rotation, rotate, rotateMap, hs, Int.cast_sub, hA,
        add_sub_assoc, Prod.add_def]
  | inr s =>
      cases s with
      | inl cy =>
          rcases cy with ⟨c, y⟩
          rw [hs] at hback
          simp [twoActivationEquiv, twoLabelEquiv, sourceResidueEquiv,
            BlockShiftData.blockInverseEquiv, BlockShiftData.blockForward,
            twoForward, usefulTwo, highTwo, sharedOutput, rotation, rotate, rotateMap,
            hs, hback, Int.cast_sub, hOther]
      | inr cyz =>
          rcases cyz with ⟨c, y, z⟩
          simp [twoActivationEquiv, twoLabelEquiv, sourceResidueEquiv,
            inactiveEquiv, inactiveForward, twoForward, usefulTwo, highTwo,
            sharedOutput, rotation, rotate, rotateMap, hs, Int.cast_sub, hA, hOther,
            add_sub_assoc, Prod.add_def]

theorem oneForward_bijective
    (D : LabeledBlocks K A B 2 b) (S : BlockShiftData Δ 2 b)
    (e : R ≃ LabelledResidue m) (code : R ≃ ZMod n)
    (H : (K × Δ) × R → ℤ)
    (hA : ∀ v, (H v : ZMod 2) = S.rhoA v.1.2)
    (hB : ∀ v, (H v : ZMod b) = S.rhoB v.1.2)
    (hOther : ∀ v, (H v : ZMod 3) = 0) (x : ℤ) (sx : R) (k : K) :
    Function.Bijective (oneForward D S e code H x sx k) := by
  have he : oneForward D S e code H x sx k =
      oneActivationEquiv D S e code H hA hB x sx k :=
    funext fun v => (oneActivationEquiv_apply D S e code H hA hB hOther x sx k v).symm
  rw [he]
  exact (oneActivationEquiv D S e code H hA hB x sx k).bijective

theorem twoForward_bijective
    (D : LabeledBlocks K A B 3 b) (S : BlockShiftData Δ 3 b)
    (e : R ≃ LabelledResidue m) (code : R ≃ ZMod n)
    (H : (K × Δ) × R → ℤ)
    (hA : ∀ v, (H v : ZMod 3) = S.rhoA v.1.2)
    (hB : ∀ v, (H v : ZMod b) = S.rhoB v.1.2)
    (hOther : ∀ v, (H v : ZMod 2) = 0) (x : ℤ) (sx : R) (k : K) :
    Function.Bijective (twoForward D S e code H x sx k) := by
  have he : twoForward D S e code H x sx k =
      twoActivationEquiv D S e code H hA hB x sx k :=
    funext fun v => (twoActivationEquiv_apply D S e code H hA hB hOther x sx k v).symm
  rw [he]
  exact (twoActivationEquiv D S e code H hA hB x sx k).bijective

end PeriodicTilingThree.SharedSeed

end

end OAI
