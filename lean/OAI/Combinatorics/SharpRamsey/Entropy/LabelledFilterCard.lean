import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.CompleteProgramWeight

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.SelectionBridge
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.CertificateCover SharpRamseyFive.WeightedPrograms
open Classical
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]
omit [DecidableEq V] [DecidableEq H] in
lemma labelled_filter_card (P : H → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun x : H × V => P x.1)).card =
      (Finset.univ.filter P).card * Fintype.card V := by
  have he : Finset.univ.filter (fun x : H × V => P x.1) =
      (Finset.univ.filter P) ×ˢ (Finset.univ : Finset V) := by
    ext z
    simp
  rw [he, Finset.card_product, Finset.card_univ]
omit [DecidableEq V] in

lemma vertexBadMass_nonneg (weight rate : D → ℝ≥0) (s : V → Finset D)
    (t : ℝ) (R J : ℕ) (A : Finset V) : 0 ≤ vertexBadMass weight rate s t R J A := by
  unfold vertexBadMass
  exact badMass_nonneg _ _ (blockTrunc_range _ R J none) _ A

theorem all_bad_residual_sum_le (weight rate : D → ℝ≥0) (lines : H → Finset D)
    (t : ℝ) (R : ℕ) (denom b mass : ℝ)
    (hd : 0 < denom) (hb : 1 ≤ b) (hm : 0 ≤ mass)
    (hmass : ∀ u, ∑ d ∈ lines u, (rate d : ℝ) ≤ mass)
    (K J h N₁ N₂ : ℕ) (hK : 2 ≤ K) (hh : 0 < h) (low : Bool)
    (hsize : h ≤ (R / 2 - if low then 0 else J) / (2 * K))
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2)
    (hN₁ : ∀ d, (Finset.univ.filter (fun u => d ∈ lines u)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun u => d ∈ lines u ∧ e ∈ lines u)).card ≤ N₂)
    (A : Finset V) (g : V → H) :
    (∑ f : V → H, if (∀ v ∉ A, g v = f v) then
      vertexBadMass weight rate (lines ∘ f) t R J A else 0) ≤
      denom ^ A.card * ∑ n : Fin (A.card + 1),
        branchingBound (V := V) (B := Fin R) (fun z : H × V => lines z.1)
          rate denom b mass K (N₁ * Fintype.card V) (N₂ * Fintype.card V) low ^ n.val := by
  let F : (V → H × V) → ℝ := fun f =>
    if Function.Injective f ∧ (∀ v ∉ A, labelled g v = f v) then
      vertexBadMass weight rate ((fun z : H × V => lines z.1) ∘ f) t R J A else 0
  have hF (f : V → H × V) : 0 ≤ F f := by
    dsimp [F]
    split_ifs
    · exact vertexBadMass_nonneg weight rate _ t R J A
    · exact le_rfl
  have he (f : V → H) : F (labelled f) =
      if (∀ v ∉ A, g v = f v) then vertexBadMass weight rate (lines ∘ f) t R J A else 0 := by
    have ha : (∀ v ∉ A, labelled g v = labelled f v) ↔ (∀ v ∉ A, g v = f v) := by
      simp only [labelled, Prod.mk.injEq, and_true]
    simp only [F, labelled_injective, true_and, ha]
    rfl
  calc
    _ = ∑ f : V → H, F (labelled f) := by simp only [he]
    _ = ∑ f ∈ Finset.univ.image (labelled : (V → H) → (V → H × V)), F f := by
      rw [Finset.sum_image (fun _ _ _ _ h => labelled_map_injective h)]
    _ ≤ ∑ f : V → H × V, F f :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun f _ _ => hF f)
    _ ≤ _ := by
      apply bad_residual_sum_le weight rate (fun z : H × V => lines z.1) t R
        denom b mass hd hb hm (fun u => hmass u.1) K J h
        (N₁ * Fintype.card V) (N₂ * Fintype.card V) hK hh low hsize herr
      · intro d
        exact (labelled_filter_card (V := V) (H := H) (fun u => d ∈ lines u)).le.trans
          (Nat.mul_le_mul_right _ (hN₁ d))
      · intro d e hde
        exact (labelled_filter_card (V := V) (H := H) (fun u => d ∈ lines u ∧ e ∈ lines u)).le.trans
          (Nat.mul_le_mul_right _ (hN₂ d e hde))

end SharpRamseyFive.SelectionBridge

namespace SharpRamseyFive.ResidualElimination
open scoped BigOperators
open Classical
variable {V H : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

def Agrees (E : Finset V) (g f : V → H) : Prop := ∀ v ∉ E, f v = g v

noncomputable def completionSum (E : Finset V) (g : V → H) (F : (V → H) → ℝ) : ℝ :=
  ∑ f : V → H, if Agrees E g f then F f else 0

omit [DecidableEq H] in
lemma completionSum_nonneg (E : Finset V) (g : V → H) (F : (V → H) → ℝ)
    (hF : ∀ f, 0 ≤ F f) : 0 ≤ completionSum E g F := by
  apply Finset.sum_nonneg
  intro f _
  split_ifs
  · exact hF f
  · exact le_rfl

omit [DecidableEq H] in
lemma completionSum_mono (E : Finset V) (g : V → H) (F G : (V → H) → ℝ)
    (h : ∀ f, Agrees E g f → F f ≤ G f) :
    completionSum E g F ≤ completionSum E g G := by
  apply Finset.sum_le_sum
  intro f _
  split_ifs with hf
  · exact h f hf
  · exact le_rfl
omit [DecidableEq H] in

lemma completionSum_congr (E : Finset V) (g : V → H) (F G : (V → H) → ℝ)
    (h : ∀ f, Agrees E g f → F f = G f) :
    completionSum E g F = completionSum E g G := by
  apply le_antisymm <;> apply completionSum_mono
  · exact fun f hf => le_of_eq (h f hf)
  · exact fun f hf => le_of_eq (h f hf).symm

omit [DecidableEq H] in
lemma completionSum_mul (E : Finset V) (g : V → H) (c : ℝ) (F : (V → H) → ℝ) :
    completionSum E g (fun f => c * F f) = c * completionSum E g F := by
  simp only [completionSum, Finset.mul_sum, mul_ite, mul_zero]

omit [DecidableEq H] in
lemma completionSum_sum {ι : Type} (T : Finset ι) (E : Finset V) (g : V → H)
    (F : ι → (V → H) → ℝ) :
    completionSum E g (fun f => ∑ i ∈ T, F i f) =
      ∑ i ∈ T, completionSum E g (F i) := by
  unfold completionSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  by_cases h : Agrees E g f <;> simp [h]

omit [Fintype V] [Fintype H] [DecidableEq H] in
lemma agrees_erase_iff (E : Finset V) (g f : V → H) {u : V} (hu : u ∈ E) (x : H) :
    Agrees (E.erase u) (Function.update g u x) f ↔ Agrees E g f ∧ f u = x := by
  constructor
  · intro h
    constructor
    · intro v hv
      have hvu : v ≠ u := by intro he; exact hv (he ▸ hu)
      simpa only [Function.update_of_ne hvu] using h v (by simp [hv])
    · simpa using h u (Finset.notMem_erase u E)
  · rintro ⟨h, hx⟩ v hv
    by_cases hvu : v = u
    · subst v; simpa using hx
    · rw [Function.update_of_ne hvu]
      exact h v (by simpa [hvu] using hv)

lemma completionSum_expose (E : Finset V) (g : V → H) {u : V} (hu : u ∈ E)
    (F : (V → H) → ℝ) :
    completionSum E g F = ∑ x : H, completionSum (E.erase u) (Function.update g u x) F := by
  unfold completionSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  simp only [agrees_erase_iff E g f hu]
  by_cases h : Agrees E g f
  · simp [h, eq_comm]
  · simp [h]

lemma completionSum_empty (g : V → H) (F : (V → H) → ℝ) :
    completionSum ∅ g F = F g := by
  have he (f : V → H) : Agrees ∅ g f ↔ f = g := by
    constructor
    · intro h
      funext v
      exact h v (Finset.notMem_empty v)
    · rintro rfl v _
      rfl
  simp [completionSum, he]

noncomputable def term (a : V → (V → H) → ℝ) (B : Finset V → (V → H) → ℝ)
    (E S : Finset V) (f : V → H) : ℝ := (∏ u ∈ S, a u f) * B (E \ S) f

omit [Fintype V] [Fintype H] [DecidableEq H] in
lemma term_nonneg (a : V → (V → H) → ℝ) (B : Finset V → (V → H) → ℝ)
    (ha : ∀ u f, 0 ≤ a u f) (hB : ∀ A f, 0 ≤ B A f)
    (E S : Finset V) (f : V → H) : 0 ≤ term a B E S f :=
  mul_nonneg (Finset.prod_nonneg (fun u _ => ha u f)) (hB _ f)

omit [Fintype V] in
lemma prod_erase_le (a : V → ℝ) (ha : ∀ u, a u ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset V) (v : V) : (∏ u ∈ S, a u) ≤ ∏ u ∈ S.erase v, a u := by
  by_cases hv : v ∈ S
  · rw [← Finset.mul_prod_erase S a hv]
    exact mul_le_of_le_one_left (Finset.prod_nonneg (fun u _ => (ha u).1)) (ha v).2
  · rw [Finset.erase_eq_of_notMem hv]

omit [Fintype V] in
lemma erase_sdiff (E S : Finset V) (u _v : V) (hu : u ∈ S) :
    E.erase u \ S.erase u = E \ S := by
  ext w
  by_cases hw : w = u <;> simp [hw, hu]

omit [Fintype V] in
lemma double_erase_sdiff (E S : Finset V) (u v : V) (hu : u ∈ S) :
    (E.erase u).erase v \ (S.erase u).erase v = (E \ S).erase v := by
  ext w
  by_cases hwu : w = u <;> by_cases hwv : w = v <;> simp [hwu, hwv, hu]

omit [Fintype H] [DecidableEq H] in
lemma term_shift_step (a : V → (V → H) → ℝ) (B : Finset V → (V → H) → ℝ)
    (W : H → H → ℝ) (ha : ∀ u f, a u f ∈ Set.Icc (0 : ℝ) 1)
    (hW : ∀ x y, 0 ≤ W x y) (hB : ∀ A f, 0 ≤ B A f)
    (hmono : ∀ A A', A' ⊆ A → ∀ f, B A f ≤ B A' f)
    (hshift : ∀ u f, a u f ≤ ∑ v ∈ Finset.univ.erase u, W (f u) (f v))
    (E S : Finset V) {u : V} (hu : u ∈ S) (f : V → H) :
    term a B E S f ≤ ∑ v ∈ Finset.univ.erase u,
      W (f u) (f v) * term a B ((E.erase u).erase v) ((S.erase u).erase v) f := by
  have hp : 0 ≤ (∏ w ∈ S.erase u, a w f) * B (E \ S) f :=
    mul_nonneg (Finset.prod_nonneg (fun w _ => (ha w f).1)) (hB _ f)
  calc
    term a B E S f = a u f * ((∏ w ∈ S.erase u, a w f) * B (E \ S) f) := by
      rw [term, ← Finset.mul_prod_erase S (fun w => a w f) hu, mul_assoc]
    _ ≤ (∑ v ∈ Finset.univ.erase u, W (f u) (f v)) *
        ((∏ w ∈ S.erase u, a w f) * B (E \ S) f) :=
      mul_le_mul_of_nonneg_right (hshift u f) hp
    _ = ∑ v ∈ Finset.univ.erase u, W (f u) (f v) *
        ((∏ w ∈ S.erase u, a w f) * B (E \ S) f) := by rw [Finset.sum_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro v hv
      apply mul_le_mul_of_nonneg_left _ (hW _ _)
      unfold term
      rw [double_erase_sdiff E S u v hu]
      apply mul_le_mul (prod_erase_le (fun w => a w f) (fun w => ha w f) _ v)
        (hmono _ _ (Finset.erase_subset v _) f) (hB _ f)
      exact Finset.prod_nonneg (fun w _ => (ha w f).1)

lemma sum_known_partner (E : Finset V) (g : V → H) {u v : V} (hu : u ∈ E) (hv : v ∉ E)
    (W : H → H → ℝ) (F : (V → H) → ℝ) (X C : ℝ)
    (hW : ∀ x y, 0 ≤ W x y) (hX : 0 ≤ X)
    (hrow : ∑ x : H, W x (g v) ≤ C)
    (hF : ∀ x : H, completionSum (E.erase u) (Function.update g u x) F ≤ X) :
    completionSum E g (fun f => W (f u) (f v) * F f) ≤ C * X := by
  rw [completionSum_expose E g hu]
  calc
    _ ≤ ∑ x : H, W x (g v) * X := by
      apply Finset.sum_le_sum
      intro x _
      have he : completionSum (E.erase u) (Function.update g u x)
          (fun f => W (f u) (f v) * F f) = W x (g v) *
            completionSum (E.erase u) (Function.update g u x) F := by
        rw [← completionSum_mul]
        apply completionSum_congr
        intro f hf
        have hfu : f u = x := by simpa using hf u (Finset.notMem_erase u E)
        have hvu : v ≠ u := by intro he; exact hv (he ▸ hu)
        have hfv : f v = g v := by
          simpa only [Function.update_of_ne hvu] using hf v (by simp [hv])
        rw [hfu, hfv]
      rw [he]
      exact mul_le_mul_of_nonneg_left (hF x) (hW _ _)
    _ = (∑ x : H, W x (g v)) * X := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hrow hX

lemma sum_new_partner (E : Finset V) (g : V → H) {u v : V}
    (hu : u ∈ E) (hv : v ∈ E) (hne : v ≠ u)
    (W : H → H → ℝ) (F : (V → H) → ℝ) (X C : ℝ)
    (hW : ∀ x y, 0 ≤ W x y) (hX : 0 ≤ X)
    (hpair : (∑ x : H, ∑ y : H, W x y) ≤ C)
    (hF : ∀ x y : H, completionSum ((E.erase u).erase v)
      (Function.update (Function.update g u x) v y) F ≤ X) :
    completionSum E g (fun f => W (f u) (f v) * F f) ≤ C * X := by
  rw [completionSum_expose E g hu]
  have hv' : v ∈ E.erase u := Finset.mem_erase.mpr ⟨hne,hv⟩
  calc
    _ ≤ ∑ x : H, ∑ y : H, W x y * X := by
      apply Finset.sum_le_sum
      intro x _
      rw [completionSum_expose _ _ hv']
      apply Finset.sum_le_sum
      intro y _
      have he : completionSum ((E.erase u).erase v)
          (Function.update (Function.update g u x) v y)
          (fun f => W (f u) (f v) * F f) = W x y *
            completionSum ((E.erase u).erase v)
              (Function.update (Function.update g u x) v y) F := by
        rw [← completionSum_mul]
        apply completionSum_congr
        intro f hf
        have hfu : f u = x := by
          simpa only [Function.update_of_ne hne.symm, Function.update_self] using
            hf u (by simp)
        have hfv : f v = y := by simpa using hf v (by simp)
        rw [hfu, hfv]
      rw [he]
      exact mul_le_mul_of_nonneg_left (hF x y) (hW _ _)
    _ = (∑ x : H, ∑ y : H, W x y) * X := by simp only [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hpair hX

theorem shift_bad_enumeration (a : V → (V → H) → ℝ) (B : Finset V → (V → H) → ℝ)
    (W : H → H → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ u f, a u f ∈ Set.Icc (0 : ℝ) 1)
    (hW : ∀ x y, 0 ≤ W x y) (hB : ∀ A f, 0 ≤ B A f)
    (hmono : ∀ A A', A' ⊆ A → ∀ f, B A f ≤ B A' f)
    (hshift : ∀ u f, a u f ≤ ∑ v ∈ Finset.univ.erase u, W (f u) (f v))
    (hrow : ∀ y, (∑ x : H, W x y) ≤ C)
    (hpair : (∑ x : H, ∑ y : H, W x y) ≤ C ^ 2)
    (hbad : ∀ A g, completionSum A g (B A) ≤ C ^ A.card)
    (E S : Finset V) (hS : S ⊆ E) (g : V → H) :
    completionSum E g (term a B E S) ≤ ((Fintype.card V + 1 : ℝ) * C) ^ E.card := by
  let M : ℝ := (Fintype.card V + 1) * C
  have hCM : C ≤ M := by dsimp [M]; nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card V)]
  have hM : 0 ≤ M := hC.trans hCM
  suffices hall : ∀ E : Finset V, ∀ S, S ⊆ E → ∀ g : V → H,
      completionSum E g (term a B E S) ≤ M ^ E.card from hall E S hS g
  intro E
  refine Finset.strongInductionOn E ?_
  intro E ih S hS g
  by_cases hs : S = ∅
  · subst S
    have he : term a B E ∅ = B E := by
      funext f
      simp [term]
    rw [he]
    exact (hbad E g).trans (pow_le_pow_left₀ hC hCM _)
  obtain ⟨u,hu⟩ := Finset.nonempty_iff_ne_empty.mpr hs
  have huE := hS hu
  have hsub := Finset.erase_ssubset huE
  have hS' : S.erase u ⊆ E.erase u := Finset.erase_subset_erase u hS
  have hcard : E.card = (E.erase u).card + 1 := (Finset.card_erase_add_one huE).symm
  calc
    _ ≤ completionSum E g (fun f => ∑ v ∈ Finset.univ.erase u,
        W (f u) (f v) * term a B ((E.erase u).erase v) ((S.erase u).erase v) f) := by
      apply completionSum_mono
      intro f _
      exact term_shift_step a B W ha hW hB hmono hshift E S hu f
    _ = ∑ v ∈ Finset.univ.erase u, completionSum E g
        (fun f => W (f u) (f v) * term a B ((E.erase u).erase v) ((S.erase u).erase v) f) :=
      completionSum_sum _ E g _
    _ ≤ ∑ _v ∈ Finset.univ.erase u, C * M ^ (E.erase u).card := by
      apply Finset.sum_le_sum
      intro v hv
      have hne : v ≠ u := (Finset.mem_erase.mp hv).1
      by_cases hvE : v ∈ E
      · have hv' : v ∈ E.erase u := Finset.mem_erase.mpr ⟨hne,hvE⟩
        have hsmall : (E.erase u).erase v ⊂ E :=
          Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset _ _) hsub
        have hSt : (S.erase u).erase v ⊆ (E.erase u).erase v :=
          Finset.erase_subset_erase v hS'
        have hbnd := sum_new_partner E g huE hvE hne W
          (term a B ((E.erase u).erase v) ((S.erase u).erase v))
          (M ^ ((E.erase u).erase v).card) (C ^ 2) hW (pow_nonneg hM _) hpair
          (fun x y => ih _ hsmall _ hSt _)
        apply hbnd.trans
        rw [show (E.erase u).card = ((E.erase u).erase v).card + 1 from
          (Finset.card_erase_add_one hv').symm, pow_succ M]
        calc
          _ = (C * C) * M ^ ((E.erase u).erase v).card := by ring
          _ ≤ (C * M) * M ^ ((E.erase u).erase v).card :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCM hC) (pow_nonneg hM _)
          _ = _ := by ring
      · have hvS : v ∉ S := fun h => hvE (hS h)
        rw [Finset.erase_eq_of_notMem (fun h => hvE (Finset.erase_subset u E h)),
          Finset.erase_eq_of_notMem (fun h => hvS (Finset.erase_subset u S h))]
        exact sum_known_partner E g huE hvE W (term a B (E.erase u) (S.erase u))
          (M ^ (E.erase u).card) C hW (pow_nonneg hM _) (hrow (g v))
          (fun x => ih _ hsub _ hS' _)
    _ ≤ M * M ^ (E.erase u).card := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hM _)
      change ((Finset.univ.erase u).card : ℝ) * C ≤ M
      have hc : ((Finset.univ.erase u).card : ℝ) ≤ (Fintype.card V : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.erase_subset u (Finset.univ : Finset V))
      dsimp [M]
      nlinarith
    _ = _ := by rw [hcard, pow_succ]; ring

end SharpRamseyFive.ResidualElimination

namespace SharpRamseyFive.SingletonEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.SelectionBridge SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.ResidualElimination
open Classical
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]
omit [DecidableEq V] in

lemma vertexBadMass_antitone (weight rate : D → ℝ≥0) (s : V → Finset D)
    (t : ℝ) (R J : ℕ) {A A' : Finset V} (hA : A' ⊆ A) :
    vertexBadMass weight rate s t R J A ≤ vertexBadMass weight rate s t R J A' := by
  unfold vertexBadMass badMass
  apply integral_mono
    (badTerm_integrable _ _ (blockTrunc_range _ R J none) _ A)
    (badTerm_integrable _ _ (blockTrunc_range _ R J none) _ A')
  intro z
  apply mul_le_mul_of_nonneg_left _ (blockTrunc_range _ R J none z).1
  exact Finset.prod_le_prod_of_subset_of_le_one₀ hA
    (fun v _ => (badIndicator_range _ v z).1)
    (fun v _ _ => (badIndicator_range _ v z).2)

lemma sum_powers_le (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), x ^ i) ≤ (1 + x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc
      _ ≤ (1 + x) ^ n + x ^ (n + 1) := add_le_add ih le_rfl
      _ ≤ (1 + x) ^ n + x * (1 + x) ^ n := by
        rw [pow_succ']
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hx (by linarith : x ≤ 1 + x) n) hx)
      _ = _ := by rw [pow_succ]; ring

lemma actual_bad_completion (weight rate : D → ℝ≥0) (lines : H → Finset D)
    (t : ℝ) (R : ℕ) (denom b mass : ℝ)
    (hd : 0 < denom) (hb : 1 ≤ b) (hm : 0 ≤ mass)
    (hmass : ∀ u, ∑ d ∈ lines u, (rate d : ℝ) ≤ mass)
    (K J h N₁ N₂ : ℕ) (hK : 2 ≤ K) (hh : 0 < h) (low : Bool)
    (hsize : h ≤ (R / 2 - if low then 0 else J) / (2 * K))
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2)
    (hN₁ : ∀ d, (Finset.univ.filter (fun u => d ∈ lines u)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun u => d ∈ lines u ∧ e ∈ lines u)).card ≤ N₂)
    (A : Finset V) (g : V → H) :
    completionSum A g (fun f => vertexBadMass weight rate (lines ∘ f) t R J A) ≤
      (denom * (1 + branchingBound (V := V) (B := Fin R)
        (fun z : H × V => lines z.1) rate denom b mass K
        (N₁ * Fintype.card V) (N₂ * Fintype.card V) low)) ^ A.card := by
  have he : completionSum A g (fun f => vertexBadMass weight rate (lines ∘ f) t R J A) =
      ∑ f : V → H, if (∀ v ∉ A, g v = f v) then
        vertexBadMass weight rate (lines ∘ f) t R J A else 0 := by
    unfold completionSum
    apply Finset.sum_congr rfl
    intro f _
    have : Agrees A g f ↔ (∀ v ∉ A, g v = f v) := by
      simp only [Agrees, eq_comm]
    simp only [this]
  rw [he]
  apply (all_bad_residual_sum_le weight rate lines t R denom b mass hd hb hm hmass
    K J h N₁ N₂ hK hh low hsize herr hN₁ hN₂ A g).trans
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hd.le _)
  rw [Fin.sum_univ_eq_sum_range]
  apply sum_powers_le
  exact branchingBound_nonneg _ _ _ _ _ hd.le (by linarith) hm _ _ _ _

noncomputable def shiftKernel (weight : D → ℝ≥0) (lines : H → Finset D) (p K : ℕ)
    (x y : H) : ℝ := min 1 (((p : ℝ) * mass weight (lines x ∩ lines y)) ^ K)

omit [Fintype H] [DecidableEq H] in
omit [Fintype D] in
lemma shiftKernel_range (weight : D → ℝ≥0) (lines : H → Finset D) (p K : ℕ)
    (x y : H) : shiftKernel weight lines p K x y ∈ Set.Icc (0 : ℝ) 1 := by
  unfold shiftKernel
  exact ⟨le_min zero_le_one (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (mass_nonneg _ _)) _),
    min_le_left _ _⟩

end SharpRamseyFive.SingletonEnumeration
end

end OAI
