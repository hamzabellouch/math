import OAI.NumberTheory.Ostmann.Arithmetic.DiagonalSmallResidueNormProduct

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.DiagonalSmallResidueNorm
open scoped BigOperators
open Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pairPiEquiv (A B : ι → Type*) :
    ((∀ i, A i) × (∀ i, B i)) ≃ (∀ i, A i × B i) where
  toFun z i := (z.1 i, z.2 i)
  invFun z := (fun i => (z i).1, fun i => (z i).2)
  left_inv _ := rfl
  right_inv _ := rfl

def crtPairEquiv (p : ι → ℕ)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j))) :
    (ZMod (∏ i, p i) × (ZMod (∏ i, p i))ˣ) ≃ LocalPair p :=
  ((ZMod.prodEquivPi p hcop).toEquiv.prodCongr
    (Supply.crtUnitsEquiv p hcop).toEquiv).trans (pairPiEquiv _ _)

omit [DecidableEq ι] in
@[simp] theorem crtPairEquiv_fst (p : ι → ℕ)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (z : ZMod (∏ i, p i) × (ZMod (∏ i, p i))ˣ) (i : ι) :
    (crtPairEquiv p hcop z i).1 =
      ZMod.castHom (Finset.dvd_prod_of_mem p (Finset.mem_univ i)) (ZMod (p i)) z.1 :=
  ZMod.prodEquivPi_apply p hcop z.1 i

omit [DecidableEq ι] in
@[simp] theorem crtPairEquiv_snd_coe (p : ι → ℕ)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (z : ZMod (∏ i, p i) × (ZMod (∏ i, p i))ˣ) (i : ι) :
    ((crtPairEquiv p hcop z i).2 : ZMod (p i)) =
      ZMod.castHom (Finset.dvd_prod_of_mem p (Finset.mem_univ i)) (ZMod (p i))
        (z.2 : ZMod (∏ i, p i)) :=
  Supply.crtUnitsEquiv_apply p hcop z.2 i

def crtTest (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (retained : ι → Bool) (g : ∀ i, ZMod (p i) → ℂ)
    (a : ∀ i, (ZMod (p i))ˣ)
    (z : ZMod (∏ i, p i) × (ZMod (∏ i, p i))ˣ) : ℝ :=
  productTest p retained g a (crtPairEquiv p hcop z)

omit [DecidableEq ι] in
theorem crtTest_eq_casts (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (retained : ι → Bool) (g : ∀ i, ZMod (p i) → ℂ)
    (a : ∀ i, (ZMod (p i))ˣ)
    (z : ZMod (∏ i, p i) × (ZMod (∏ i, p i))ˣ) :
    crtTest p hcop retained g a z = ∏ i,
      let reduce := ZMod.castHom (Finset.dvd_prod_of_mem p (Finset.mem_univ i)) (ZMod (p i))
      if retained i then ‖g i ((a i : ZMod (p i)) /
        (reduce z.1 * reduce (z.2 : ZMod (∏ i, p i))))‖^2
      else if IsUnit (reduce z.1) then 1 else 0 := by
  simp only [crtTest, productTest, localFactor, transformFactor, unitFactor,
    crtPairEquiv_fst, crtPairEquiv_snd_coe]

theorem crtTest_average (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (retained : ι → Bool) (g : ∀ i, ZMod (p i) → ℂ)
    (hg0 : ∀ i, g i 0 = 0)
    (hgnorm : ∀ i, ∑ x : ZMod (p i), ‖g i x‖^2 = (p i : ℝ))
    (a : ∀ i, (ZMod (p i))ˣ) :
    (∑ z : ZMod (∏ i, p i) × (ZMod (∏ i, p i))ˣ, crtTest p hcop retained g a z) /
      Fintype.card (ZMod (∏ i, p i) × (ZMod (∏ i, p i))ˣ) =
      ∏ i, localDensity (p i) (retained i) := by
  change (∑ z, productTest p retained g a (crtPairEquiv p hcop z)) / _ = _
  rw [(crtPairEquiv p hcop).sum_comp (productTest p retained g a),
    Fintype.card_congr (crtPairEquiv p hcop)]
  exact productTest_average p retained g hg0 hgnorm a

theorem actual_crtTest_average (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (d : Decomposition) (retained : ι → Bool) (a : ∀ i, (ZMod (p i))ˣ) :
    (∑ z : ZMod (∏ i, p i) × (ZMod (∏ i, p i))ˣ,
      crtTest p hcop retained (fun i => residueTransform d (p i)) a z) /
      Fintype.card (ZMod (∏ i, p i) × (ZMod (∏ i, p i))ˣ) =
      ∏ i, localDensity (p i) (retained i) :=
  crtTest_average p hcop retained _
    (fun _ => by simp [residueTransform_eq, Supply.additiveTransform_zero])
    (fun i => residueTransform_sq_sum d (p i) (Fact.out : (p i).Prime)) a

end Ostmann.Arithmetic.DiagonalSmallResidueNorm

end

end OAI
