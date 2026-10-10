import OAI.Analysis.FreeGroupFactor.RankTwoWords

namespace OAI

noncomputable section

universe uG uI uJ uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

attribute [local instance] Classical.propDecidable

namespace FreeGroupFactorMain
namespace RankTwo

section

theorem top_power_dominates (B L k : ℕ) (hB : L < B) (hk : 0 < k) :
    (L : ℤ) * (B : ℤ)^(k-1) < (B : ℤ)^k := by
  have hb : (0 : ℤ) < B := by omega
  have hp : (0 : ℤ) < (B : ℤ)^(k-1) := pow_pos hb _
  calc
    _ < (B : ℤ) * (B : ℤ)^(k-1) := mul_lt_mul_of_pos_right (by exact_mod_cast hB) hp
    _ = (B : ℤ)^k := by rw [mul_comm, ← pow_succ]; congr 1; omega

theorem power_sum_ne_zero {m B L : ℕ} (hB : m * L < B)
    (c : Fin m → ℤ) (hc : ∀ i, |c i| ≤ L) (hne : ∃ i, c i ≠ 0) :
    ∑ i, c i * (B : ℤ)^i.val ≠ 0 := by
  classical
  let s : Finset (Fin m) := Finset.univ.filter (fun i => c i ≠ 0)
  have hs : s.Nonempty := by obtain ⟨i,hi⟩ := hne; exact ⟨i,by simp [s,hi]⟩
  let j := s.max' hs
  have hj : c j ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem s hs)).2
  have hm : 0 < m := by obtain ⟨i,_⟩ := hne; exact lt_of_le_of_lt (Nat.zero_le i.val) i.is_lt
  have hL : 0 < L := by
    obtain ⟨i,hi⟩ := hne
    have hci := hc i
    have : 1 ≤ |c i| := by have := abs_pos.mpr hi; omega
    omega
  have hb : (0 : ℤ) < B := by
    have : 0 < m * L := Nat.mul_pos hm hL
    omega
  have hvan (i : Fin m) (hij : j < i) : c i = 0 := by
    by_contra hi
    have him : i ∈ s := by simp [s,hi]
    exact (not_lt_of_ge (Finset.le_max' s i him)) hij
  have hsplit : (∑ i, c i * (B : ℤ)^i.val) =
      c j * (B : ℤ)^j.val + ∑ i ∈ Finset.univ.erase j, c i * (B : ℤ)^i.val := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
  rw [hsplit]
  by_cases hj0 : j.val = 0
  · have hrest : ∑ i ∈ Finset.univ.erase j, c i * (B : ℤ)^i.val = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hij : j < i := by
        have hine := (Finset.mem_erase.mp hi).1
        have hiv : i.val ≠ j.val := fun h => hine (Fin.ext h)
        change j.val < i.val
        omega
      rw [hvan i hij,zero_mul]
    simpa [hrest,hj0] using hj
  · have hrest : |∑ i ∈ Finset.univ.erase j, c i * (B : ℤ)^i.val| ≤
        (m : ℤ) * L * (B : ℤ)^(j.val-1) := by
      calc
        _ ≤ ∑ i ∈ Finset.univ.erase j, |c i * (B : ℤ)^i.val| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i ∈ Finset.univ.erase j, (L : ℤ) * (B : ℤ)^(j.val-1) := by
          apply Finset.sum_le_sum
          intro i hi
          by_cases hij : i < j
          · rw [abs_mul,abs_of_nonneg (pow_nonneg hb.le _)]
            gcongr
            · exact hc i
            · exact_mod_cast (by omega : i.val ≤ j.val-1)
          · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij)
                (by exact (Finset.mem_erase.mp hi).1.symm)
            rw [hvan i hji,zero_mul,abs_zero]
            positivity
        _ ≤ (m : ℤ) * L * (B : ℤ)^(j.val-1) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          have hcard : ((Finset.univ.erase j).card : ℤ) ≤ m := by
            exact_mod_cast (show (Finset.univ.erase j).card ≤ m by simp only [Finset.card_erase_of_mem (Finset.mem_univ j),Finset.card_univ,Fintype.card_fin]; omega)
          have hn : 0 ≤ (L : ℤ) * (B : ℤ)^(j.val-1) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hcard hn]
    have hdom : (m : ℤ) * L * (B : ℤ)^(j.val-1) < (B : ℤ)^j.val := by
      simpa [Nat.cast_mul] using top_power_dominates B (m*L) j.val hB (Nat.pos_of_ne_zero hj0)
    have hlead : (B : ℤ)^j.val ≤ |c j * (B : ℤ)^j.val| := by
      rw [abs_mul,abs_of_nonneg (pow_nonneg hb.le _)]
      have hci : 1 ≤ |c j| := by have := abs_pos.mpr hj; omega
      nlinarith [pow_nonneg hb.le j.val]
    intro heq
    have habs : |c j * (B : ℤ)^j.val| =
        |∑ i ∈ Finset.univ.erase j, c i * (B : ℤ)^i.val| := by
      have := eq_neg_of_add_eq_zero_left heq
      rw [this,abs_neg]
    omega

def bExponentHom : SyllableGroup →* Multiplicative ℤ :=
  Monoid.CoprodI.lift (fun i => if i then 1 else MonoidHom.id _)

def bExponent (g : SyllableGroup) : ℤ := Multiplicative.toAdd (bExponentHom g)

@[simp] theorem bExponent_one : bExponent 1 = 0 := by simp [bExponent]
@[simp] theorem bExponent_mul (g h : SyllableGroup) : bExponent (g*h) = bExponent g+bExponent h := by
  simp [bExponent]
@[simp] theorem bExponent_inv (g : SyllableGroup) : bExponent g⁻¹ = -bExponent g := by
  simp [bExponent]
@[simp] theorem bExponent_a (z : ℤ) : bExponent (syllable true z) = 0 := by
  simp [bExponent,bExponentHom,syllable]
@[simp] theorem bExponent_b (z : ℤ) : bExponent (syllable false z) = z := by
  simp [bExponent,bExponentHom,syllable]
@[simp] theorem bExponent_piece (E : ℕ → ℤ) (j : ℕ) : bExponent (piece E j) = E j := by
  simp [piece]

theorem bExponent_segment (B k : ℕ) :
    bExponent (segment (runExponent B) 0 k) = (B : ℤ)^k-1 := by
  induction k with
  | zero => simp
  | succ k ih => simp only [segment_succ,bExponent_mul,bExponent_piece,zero_add,ih]
                 simp only [runExponent,pow_succ]
                 ring

def boolSign (b : Bool) : ℤ := if b then 1 else -1

@[simp] theorem boolSign_true : boolSign true = 1 := rfl
@[simp] theorem boolSign_false : boolSign false = -1 := rfl
@[simp] theorem boolSign_not (b : Bool) : boolSign (!b) = -boolSign b := by cases b <;> rfl
@[simp] theorem abs_boolSign (b : Bool) : |boolSign b| = 1 := by cases b <;> norm_num [boolSign]

def labelCoefficient {I : Type uI} [Fintype I] {m : ℕ}
    (b : I → Bool) (x : I → Fin m) (j : Fin m) : ℤ :=
  ∑ i, if x i = j then boolSign (b i) else 0

theorem labelCoefficient_abs_le {I : Type uI} [Fintype I] {m : ℕ}
    (b : I → Bool) (x : I → Fin m) (j : Fin m) :
    |labelCoefficient b x j| ≤ Fintype.card I := by
  classical
  unfold labelCoefficient
  calc
    _ ≤ ∑ i, |if x i = j then boolSign (b i) else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : I, (1 : ℤ) := by apply Finset.sum_le_sum; intro i _; split_ifs <;> simp
    _ = _ := by simp

theorem labelCoefficient_sum_mul {I : Type uI} [Fintype I] {m : ℕ}
    (b : I → Bool) (x : I → Fin m) (f : Fin m → ℤ) :
    ∑ j, labelCoefficient b x j * f j = ∑ i, boolSign (b i)*f (x i) := by
  classical
  simp only [labelCoefficient,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [ite_mul]

theorem labelCoefficient_eq_zero {I : Type uI} [Fintype I] {m B : ℕ}
    (hB : m * Fintype.card I < B) (hb : 2 ≤ B)
    (b : I → Bool) (x : I → Fin m)
    (hcharge : ∑ i, boolSign (b i) = 0)
    (hexp : ∑ i, boolSign (b i)*((B : ℤ)^((x i).val+2)-1) = 0) :
    ∀ j, labelCoefficient b x j = 0 := by
  classical
  have hn : (B : ℤ) ≠ 0 := by omega
  have he : ∑ i, boolSign (b i)*(B : ℤ)^(x i).val = 0 := by
    have hh : ∑ i, boolSign (b i)*((B : ℤ)^((x i).val+2)-1) =
        (∑ i, boolSign (b i)*(B : ℤ)^(x i).val)*(B : ℤ)^2 - ∑ i, boolSign (b i) := by
      simp only [pow_add,mul_sub,mul_one,Finset.sum_sub_distrib,Finset.sum_mul,mul_assoc]
    rw [hh,hcharge,sub_zero] at hexp
    exact (mul_eq_zero.mp hexp).resolve_right (pow_ne_zero _ hn)
  intro j
  by_contra hj
  have hne := power_sum_ne_zero hB (labelCoefficient b x) (labelCoefficient_abs_le b x) ⟨j,hj⟩
  apply hne
  rw [labelCoefficient_sum_mul]
  exact he

def AdjacentValues {m r : ℕ} (p : Fin r → Fin m) : Prop :=
  ∃ i j, (p i).val + 1 = (p j).val

def Covers {m r : ℕ} (p q : Fin r → Fin m) : Prop := ∀ i, ∃ j, p j = q i

theorem covers_iff {m r : ℕ} (p q : Fin r → Fin m) :
    Covers p q ↔ ∃ σ : Fin r → Fin r, q = p ∘ σ := by
  classical
  constructor
  · intro h
    choose σ hσ using h
    exact ⟨σ,funext (fun i => (hσ i).symm)⟩
  · rintro ⟨σ,rfl⟩ i
    exact ⟨σ i,rfl⟩

def adjacentPairs (m r : ℕ) (i j : Fin r) : Finset (Fin r → Fin m) :=
  Finset.univ.filter (fun p => (p i).val+1 = (p j).val)

theorem card_adjacentPairs_le (m r : ℕ) (i j : Fin r) :
    (adjacentPairs m r i j).card ≤ m^(r-1) := by
  classical
  by_cases hij : i = j
  · subst j
    simp [adjacentPairs]
  · let restrict : {p // p ∈ adjacentPairs m r i j} → ({x : Fin r // x ≠ j} → Fin m) :=
      fun p x => p.val x.val
    have hinj : Function.Injective restrict := by
      intro p q hpq
      apply Subtype.ext
      funext x
      by_cases hx : x = j
      · subst x
        have hpi := (Finset.mem_filter.mp p.property).2
        have hqi := (Finset.mem_filter.mp q.property).2
        have hei : p.val i = q.val i := congrFun hpq ⟨i,hij⟩
        apply Fin.ext
        omega
      · exact congrFun hpq ⟨x,hx⟩
    have hc := Fintype.card_le_of_injective restrict hinj
    have hj : Fintype.card {x : Fin r // x ≠ j} = r-1 := by
      simp [Fintype.card_subtype_compl]
    simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin,hj] using hc

def adjacentFunctions (m r : ℕ) : Finset (Fin r → Fin m) := by
  classical
  exact Finset.univ.filter AdjacentValues

theorem adjacentFunctions_eq (m r : ℕ) :
    adjacentFunctions m r = Finset.univ.biUnion (fun i : Fin r =>
      Finset.univ.biUnion (fun j : Fin r => adjacentPairs m r i j)) := by
  classical
  ext p
  simp [adjacentFunctions,AdjacentValues,adjacentPairs]

theorem card_adjacentFunctions_le (m r : ℕ) :
    (adjacentFunctions m r).card ≤ r^2 * m^(r-1) := by
  classical
  rw [adjacentFunctions_eq]
  calc
    _ ≤ ∑ i : Fin r, (Finset.univ.biUnion (fun j : Fin r => adjacentPairs m r i j)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ i : Fin r, ∑ j : Fin r, (adjacentPairs m r i j).card :=
      Finset.sum_le_sum (fun _ _ => Finset.card_biUnion_le)
    _ ≤ ∑ _i : Fin r, ∑ _j : Fin r, m^(r-1) := by
      gcongr with i _ j _
      exact card_adjacentPairs_le m r i j
    _ = _ := by simp [pow_two,Nat.mul_assoc]

def coveredPairs (m r : ℕ) : Finset ((Fin r → Fin m) × (Fin r → Fin m)) := by
  classical
  exact Finset.univ.filter (fun p => Covers p.1 p.2)

def badCoveredPairs (m r : ℕ) : Finset ((Fin r → Fin m) × (Fin r → Fin m)) := by
  classical
  exact Finset.univ.filter (fun p => Covers p.1 p.2 ∧ AdjacentValues p.1)

theorem coveredPairs_param (m r : ℕ) :
    coveredPairs m r = Finset.univ.image (fun t : (Fin r → Fin m) × (Fin r → Fin r) =>
      (t.1,t.1 ∘ t.2)) := by
  classical
  ext ⟨p,q⟩
  constructor
  · intro h
    obtain ⟨σ,hσ⟩ := (covers_iff p q).mp (Finset.mem_filter.mp h).2
    apply Finset.mem_image.mpr
    exact ⟨(p,σ),Finset.mem_univ _,Prod.ext rfl hσ.symm⟩
  · intro h
    obtain ⟨⟨p',σ⟩,_,he⟩ := Finset.mem_image.mp h
    have hp : p' = p := congrArg Prod.fst he
    have hq : p' ∘ σ = q := congrArg Prod.snd he
    subst p'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(covers_iff p q).mpr ⟨σ,hq.symm⟩⟩

theorem card_coveredPairs_le (m r : ℕ) :
    (coveredPairs m r).card ≤ m^r * r^r := by
  classical
  rw [coveredPairs_param]
  simpa using Finset.card_image_le (s := (Finset.univ : Finset ((Fin r → Fin m) × (Fin r → Fin r))))
    (f := fun t => (t.1,t.1 ∘ t.2))

theorem badCoveredPairs_param (m r : ℕ) :
    badCoveredPairs m r = ((adjacentFunctions m r) ×ˢ (Finset.univ : Finset (Fin r → Fin r))).image
      (fun t => (t.1,t.1 ∘ t.2)) := by
  classical
  ext ⟨p,q⟩
  constructor
  · intro h
    obtain ⟨hc,ha⟩ := (Finset.mem_filter.mp h).2
    obtain ⟨σ,hσ⟩ := (covers_iff p q).mp hc
    apply Finset.mem_image.mpr
    refine ⟨(p,σ),?_,Prod.ext rfl hσ.symm⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩,Finset.mem_univ _⟩
  · intro h
    obtain ⟨⟨p',σ⟩,hm,he⟩ := Finset.mem_image.mp h
    have hp : p' = p := congrArg Prod.fst he
    have hq : p' ∘ σ = q := congrArg Prod.snd he
    subst p'
    have ha := (Finset.mem_filter.mp (Finset.mem_product.mp hm).1).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(covers_iff p q).mpr ⟨σ,hq.symm⟩,ha⟩

theorem card_badCoveredPairs_le (m r : ℕ) :
    (badCoveredPairs m r).card ≤ (r^2 * r^r) * m^(r-1) := by
  classical
  rw [badCoveredPairs_param]
  calc
    _ ≤ ((adjacentFunctions m r) ×ˢ (Finset.univ : Finset (Fin r → Fin r))).card := Finset.card_image_le
    _ = (adjacentFunctions m r).card * r^r := by simp
    _ ≤ (r^2 * m^(r-1)) * r^r := Nat.mul_le_mul_right _ (card_adjacentFunctions_le m r)
    _ = _ := by ring

variable {I : Type uI}

def coloredEncode {m r : ℕ} (b : I → Bool)
    (eP : Fin r ≃ {i // b i = true}) (eN : Fin r ≃ {i // b i = false})
    (x : I → Fin m) : (Fin r → Fin m) × (Fin r → Fin m) :=
  (fun j => x (eP j).val, fun j => x (eN j).val)

theorem coloredEncode_injective {m r : ℕ} (b : I → Bool)
    (eP : Fin r ≃ {i // b i = true}) (eN : Fin r ≃ {i // b i = false}) :
    Function.Injective (coloredEncode (m := m) b eP eN) := by
  intro x y h
  funext i
  cases hi : b i with
  | false =>
    have he := congrFun (congrArg Prod.snd h) (eN.symm ⟨i,hi⟩)
    simpa only [coloredEncode,Equiv.apply_symm_apply] using he
  | true =>
    have he := congrFun (congrArg Prod.fst h) (eP.symm ⟨i,hi⟩)
    simpa only [coloredEncode,Equiv.apply_symm_apply] using he

def ColoredCovers {m : ℕ} (b : I → Bool) (x : I → Fin m) : Prop :=
  ∀ i, b i = false → ∃ j, b j = true ∧ x j = x i

def ColoredAdjacent {m : ℕ} (b : I → Bool) (x : I → Fin m) : Prop :=
  ∃ i j, b i = true ∧ b j = true ∧ (x i).val+1 = (x j).val

theorem coloredEncode_covers {m r : ℕ} (b : I → Bool)
    (eP : Fin r ≃ {i // b i = true}) (eN : Fin r ≃ {i // b i = false})
    (x : I → Fin m) (h : ColoredCovers b x) :
    Covers (coloredEncode b eP eN x).1 (coloredEncode b eP eN x).2 := by
  intro i
  obtain ⟨j,hj,he⟩ := h (eN i).val (eN i).property
  refine ⟨eP.symm ⟨j,hj⟩,?_⟩
  simpa only [coloredEncode,Equiv.apply_symm_apply] using he

theorem coloredEncode_adjacent {m r : ℕ} (b : I → Bool)
    (eP : Fin r ≃ {i // b i = true}) (eN : Fin r ≃ {i // b i = false})
    (x : I → Fin m) (h : ColoredAdjacent b x) :
    AdjacentValues (coloredEncode b eP eN x).1 := by
  obtain ⟨i,j,hi,hj,he⟩ := h
  refine ⟨eP.symm ⟨i,hi⟩,eP.symm ⟨j,hj⟩,?_⟩
  simpa only [coloredEncode,Equiv.apply_symm_apply] using he

theorem card_coloredCovered_le {m r : ℕ} (b : I → Bool)
    (eP : Fin r ≃ {i // b i = true}) (eN : Fin r ≃ {i // b i = false})
    (s : Finset (I → Fin m)) (hs : ∀ x ∈ s, ColoredCovers b x) :
    s.card ≤ m^r * r^r := by
  classical
  have he : s.image (coloredEncode b eP eN) ⊆ coveredPairs m r := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,coloredEncode_covers b eP eN x (hs x hx)⟩
  calc
    _ = (s.image (coloredEncode b eP eN)).card := (Finset.card_image_of_injective s (coloredEncode_injective b eP eN)).symm
    _ ≤ (coveredPairs m r).card := Finset.card_le_card he
    _ ≤ _ := card_coveredPairs_le m r

theorem card_coloredBad_le {m r : ℕ} (b : I → Bool)
    (eP : Fin r ≃ {i // b i = true}) (eN : Fin r ≃ {i // b i = false})
    (s : Finset (I → Fin m))
    (hs : ∀ x ∈ s, ColoredCovers b x ∧ ColoredAdjacent b x) :
    s.card ≤ (r^2 * r^r) * m^(r-1) := by
  classical
  have he : s.image (coloredEncode b eP eN) ⊆ badCoveredPairs m r := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hc,ha⟩ := hs x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,coloredEncode_covers b eP eN x hc,
      coloredEncode_adjacent b eP eN x ha⟩
  calc
    _ = (s.image (coloredEncode b eP eN)).card := (Finset.card_image_of_injective s (coloredEncode_injective b eP eN)).symm
    _ ≤ (badCoveredPairs m r).card := Finset.card_le_card he
    _ ≤ _ := card_badCoveredPairs_le m r

end

def prefixHom (B m : ℕ) : FreeGroup (Fin m) →* SyllableGroup :=
  FreeGroup.lift (fun i => segment (runExponent B) 0 (i.val+2))

def patternWord {m l : ℕ} (b : Fin l → Bool) (x : Fin l → Fin m) : FreeGroup (Fin m) :=
  FreeGroup.mk (List.ofFn (fun i => (x i,b i)))

def pairColors {I : Type uI} {J : Type uJ} (b : I → Bool) (c : J → Bool) : I ⊕ J → Bool :=
  Sum.elim b (fun j => !(c j))

def pairLabels {I : Type uI} {J : Type uJ} {m : ℕ} (x : I → Fin m) (y : J → Fin m) : I ⊕ J → Fin m :=
  Sum.elim x y

theorem pairLabels_injective {I : Type uI} {J : Type uJ} {m : ℕ} :
    Function.Injective (fun p : (I → Fin m) × (J → Fin m) => pairLabels p.1 p.2) := by
  intro p q h
  apply Prod.ext
  · funext i; exact congrFun h (.inl i)
  · funext j; exact congrFun h (.inr j)

theorem bExponent_lift_mk {ι : Type uι} (f : ι → SyllableGroup) (L : List (ι × Bool)) :
    bExponent (FreeGroup.lift f (FreeGroup.mk L)) =
      (L.map (fun p => boolSign p.2 * bExponent (f p.1))).sum := by
  rw [FreeGroup.lift_mk]
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [Bool.cond_eq_ite] at ih
    cases p with | mk i b => cases b <;> simp [ih]

theorem bExponent_pattern (B m l : ℕ) (b : Fin l → Bool) (x : Fin l → Fin m) :
    bExponent (prefixHom B m (patternWord b x)) =
      ∑ i, boolSign (b i) * ((B : ℤ)^((x i).val+2)-1) := by
  unfold prefixHom patternWord
  rw [bExponent_lift_mk,List.map_ofFn,List.sum_ofFn]
  simp only [bExponent_segment]
  rfl

theorem covers_of_balanced {I : Type uI} [Fintype I] {m : ℕ}
    (b : I → Bool) (x : I → Fin m) (he : ∀ j, labelCoefficient b x j = 0) :
    ColoredCovers b x := by
  classical
  intro i hi
  by_contra hn
  have hno (j : I) (hj : x j = x i) : b j = false := by
    cases hb : b j with
    | false => rfl
    | true => exact False.elim (hn ⟨j,hb,hj⟩)
  have hle (j : I) : (if x j = x i then boolSign (b j) else 0 : ℤ) ≤ 0 := by
    split_ifs with hj
    · rw [hno j hj]; norm_num
    · rfl
  have hlt : (∑ j, if x j = x i then boolSign (b j) else 0 : ℤ) < ∑ _j : I, 0 := by
    apply Finset.sum_lt_sum (fun j _ => hle j)
    exact ⟨i,Finset.mem_univ _,by simp [hi]⟩
  have hz := he (x i)
  simp only [labelCoefficient] at hz
  simp only [Finset.sum_const_zero] at hlt
  omega

theorem collision_covers {m l k B : ℕ} (hB : m * (l+k) < B) (hb : 2 ≤ B)
    (b : Fin l → Bool) (c : Fin k → Bool) (x : Fin l → Fin m) (y : Fin k → Fin m)
    (hc : ∑ i, boolSign (b i) = ∑ j, boolSign (c j))
    (he : prefixHom B m (patternWord b x) = prefixHom B m (patternWord c y)) :
    ColoredCovers (pairColors b c) (pairLabels x y) := by
  have he' := congrArg bExponent he
  rw [bExponent_pattern,bExponent_pattern] at he'
  have hcharge : ∑ i, boolSign (pairColors b c i) = 0 := by
    simp only [Fintype.sum_sum_type,pairColors,Sum.elim_inl,Sum.elim_inr,boolSign_not,
      Finset.sum_neg_distrib,hc,add_neg_cancel]
  have hexp : ∑ i, boolSign (pairColors b c i)*((B : ℤ)^((pairLabels x y i).val+2)-1) = 0 := by
    simp only [Fintype.sum_sum_type,pairColors,pairLabels,Sum.elim_inl,Sum.elim_inr,
      boolSign_not,neg_mul,Finset.sum_neg_distrib,he',add_neg_cancel]
  apply covers_of_balanced
  apply labelCoefficient_eq_zero (by simpa only [Fintype.card_sum,Fintype.card_fin] using hB) hb _ _ hcharge hexp

theorem separated_of_covers {I : Type uI} {m : ℕ} (b : I → Bool) (x : I → Fin m)
    (hc : ColoredCovers b x) (ha : ¬ColoredAdjacent b x) :
    ∀ i j, (x i).val+1 ≠ (x j).val := by
  have hp (i : I) : ∃ j, b j = true ∧ x j = x i := by
    cases hi : b i with
    | false => exact hc i hi
    | true => exact ⟨i,hi,rfl⟩
  intro i j he
  obtain ⟨u,hu,heu⟩ := hp i
  obtain ⟨v,hv,hev⟩ := hp j
  exact ha ⟨u,v,hu,hv,by simpa only [heu,hev] using he⟩

theorem collision_free_of_separated {m l k B : ℕ} (hb : 2 ≤ B)
    (b : Fin l → Bool) (c : Fin k → Bool) (x : Fin l → Fin m) (y : Fin k → Fin m)
    (hs : ∀ i j, (pairLabels x y i).val+1 ≠ (pairLabels x y j).val)
    (he : prefixHom B m (patternWord b x) = prefixHom B m (patternWord c y)) :
    patternWord b x = patternWord c y := by
  let L := List.ofFn (fun i => (x i,b i)) ++ FreeGroup.invRev (List.ofFn (fun j => (y j,c j)))
  have hlabel (p : Fin m × Bool) (hp : p ∈ L) : ∃ i, pairLabels x y i = p.1 := by
    simp only [L,List.mem_append,FreeGroup.invRev,List.mem_reverse,List.mem_map,List.mem_ofFn] at hp
    rcases hp with h | ⟨q,⟨j,hj⟩,hq⟩
    · obtain ⟨i,hi⟩ := h
      exact ⟨.inl i,congrArg Prod.fst hi⟩
    · subst q
      exact ⟨.inr j,congrArg Prod.fst hq⟩
  have hsep : ∀ p ∈ L, ∀ q ∈ L, p.1.val+1 ≠ q.1.val := by
    intro p hp q hq
    obtain ⟨i,hi⟩ := hlabel p hp
    obtain ⟨j,hj⟩ := hlabel q hq
    simpa only [hi,hj] using hs i j
  have hmk : FreeGroup.mk L = patternWord b x * (patternWord c y)⁻¹ := by
    rw [patternWord,patternWord,FreeGroup.inv_mk,FreeGroup.mul_mk]
  have hrel : prefixHom B m (FreeGroup.mk L) = 1 := by
    rw [hmk,map_mul,map_inv,he,mul_inv_cancel]
  have hzero := prefixRelation_of_separated (runExponent B)
    (fun j => ne_of_gt (runExponent_pos hb j)) (runExponent_strictMono hb).injective L hsep hrel
  rw [hmk,mul_inv_eq_one] at hzero
  exact hzero

theorem collision_bad_adjacent {m l k B : ℕ} (hB : m * (l+k) < B) (hb : 2 ≤ B)
    (b : Fin l → Bool) (c : Fin k → Bool) (x : Fin l → Fin m) (y : Fin k → Fin m)
    (hc : ∑ i, boolSign (b i) = ∑ j, boolSign (c j))
    (he : prefixHom B m (patternWord b x) = prefixHom B m (patternWord c y))
    (hne : patternWord b x ≠ patternWord c y) :
    ColoredCovers (pairColors b c) (pairLabels x y) ∧
      ColoredAdjacent (pairColors b c) (pairLabels x y) := by
  have hc' := collision_covers hB hb b c x y hc he
  refine ⟨hc',?_⟩
  by_contra ha
  exact hne (collision_free_of_separated hb b c x y (separated_of_covers _ _ hc' ha) he)

theorem card_patternCollisions_le {m l k B r : ℕ} (hB : m*(l+k) < B) (hb : 2 ≤ B)
    (b : Fin l → Bool) (c : Fin k → Bool)
    (eP : Fin r ≃ {i // pairColors b c i = true})
    (eN : Fin r ≃ {i // pairColors b c i = false})
    (hc : ∑ i, boolSign (b i) = ∑ j, boolSign (c j))
    (s : Finset ((Fin l → Fin m) × (Fin k → Fin m)))
    (hs : ∀ p ∈ s, prefixHom B m (patternWord b p.1) = prefixHom B m (patternWord c p.2)) :
    s.card ≤ m^r * r^r := by
  classical
  let t := s.image (fun p => pairLabels p.1 p.2)
  have ht : ∀ x ∈ t, ColoredCovers (pairColors b c) x := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    exact collision_covers hB hb b c p.1 p.2 hc (hs p hp)
  have hh := card_coloredCovered_le (pairColors b c) eP eN t ht
  rwa [Finset.card_image_of_injective s pairLabels_injective] at hh

theorem card_patternBadCollisions_le {m l k B r : ℕ} (hB : m*(l+k) < B) (hb : 2 ≤ B)
    (b : Fin l → Bool) (c : Fin k → Bool)
    (eP : Fin r ≃ {i // pairColors b c i = true})
    (eN : Fin r ≃ {i // pairColors b c i = false})
    (hc : ∑ i, boolSign (b i) = ∑ j, boolSign (c j))
    (s : Finset ((Fin l → Fin m) × (Fin k → Fin m)))
    (hs : ∀ p ∈ s, prefixHom B m (patternWord b p.1) = prefixHom B m (patternWord c p.2) ∧
      patternWord b p.1 ≠ patternWord c p.2) :
    s.card ≤ (r^2*r^r)*m^(r-1) := by
  classical
  let t := s.image (fun p => pairLabels p.1 p.2)
  have ht : ∀ x ∈ t, ColoredCovers (pairColors b c) x ∧ ColoredAdjacent (pairColors b c) x := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    exact collision_bad_adjacent hB hb b c p.1 p.2 hc (hs p hp).1 (hs p hp).2
  have hh := card_coloredBad_le (pairColors b c) eP eN t ht
  rwa [Finset.card_image_of_injective s pairLabels_injective] at hh

theorem card_patternCollisions_le_free_add {m l k B r : ℕ} (hB : m*(l+k) < B) (hb : 2 ≤ B)
    (b : Fin l → Bool) (c : Fin k → Bool)
    (eP : Fin r ≃ {i // pairColors b c i = true})
    (eN : Fin r ≃ {i // pairColors b c i = false})
    (hc : ∑ i, boolSign (b i) = ∑ j, boolSign (c j))
    (s : Finset ((Fin l → Fin m) × (Fin k → Fin m))) :
    (s.filter (fun p => prefixHom B m (patternWord b p.1) = prefixHom B m (patternWord c p.2))).card ≤
      (s.filter (fun p => patternWord b p.1 = patternWord c p.2)).card + (r^2*r^r)*m^(r-1) := by
  classical
  let t := s.filter (fun p => prefixHom B m (patternWord b p.1) = prefixHom B m (patternWord c p.2))
  let u := t.filter (fun p => patternWord b p.1 = patternWord c p.2)
  let v := t.filter (fun p => ¬ patternWord b p.1 = patternWord c p.2)
  have huc : u.card ≤ (s.filter (fun p => patternWord b p.1 = patternWord c p.2)).card := by
    apply Finset.card_le_card
    intro p hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1,
      (Finset.mem_filter.mp hp).2⟩
  have hvc : v.card ≤ (r^2*r^r)*m^(r-1) := by
    apply card_patternBadCollisions_le hB hb b c eP eN hc v
    intro p hp
    exact ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2,(Finset.mem_filter.mp hp).2⟩
  have he : u.card+v.card = t.card := Finset.card_filter_add_card_filter_not _
  change t.card ≤ _
  omega

def alternating (b : Bool) : (l : ℕ) → Fin l → Bool
  | 0 => Fin.elim0
  | l+1 => Fin.cases b (alternating (!b) l)

@[simp] theorem alternating_zero (b : Bool) (l : ℕ) : alternating b (l+1) 0 = b := rfl
@[simp] theorem alternating_succ (b : Bool) (l : ℕ) (i : Fin l) :
    alternating b (l+1) i.succ = alternating (!b) l i := rfl

theorem signed_ofFn {ι : Type uι} (b : Bool) (l : ℕ) (x : Fin l → ι) :
    Radial.signed b (List.ofFn x) = List.ofFn (fun i => (x i,alternating b l i)) := by
  induction l generalizing b with
  | zero => simp [Radial.signed]
  | succ l ih =>
    rw [List.ofFn_succ,Radial.signed,ih,List.ofFn_succ]
    rfl

theorem vertex_ofFn {m l : ℕ} (b : Bool) (x : Fin l → Fin m) :
    Radial.vertex b (List.ofFn x) = patternWord (alternating b l) x := by
  unfold Radial.vertex patternWord
  rw [signed_ofFn]

def positiveCount (b : Bool) (l : ℕ) : ℕ := ∑ i, if alternating b l i = true then 1 else 0

@[simp] theorem positiveCount_zero (b : Bool) : positiveCount b 0 = 0 := by simp [positiveCount]
@[simp] theorem positiveCount_succ (b : Bool) (l : ℕ) :
    positiveCount b (l+1) = (if b = true then 1 else 0)+positiveCount (!b) l := by
  simp only [positiveCount,Fin.sum_univ_succ,alternating_zero,alternating_succ]
  rfl

theorem positiveCount_two (b : Bool) (l : ℕ) : positiveCount b (l+2) = 1+positiveCount b l := by
  rw [positiveCount_succ,positiveCount_succ]
  cases b <;> simp

theorem positiveCount_even (b : Bool) (k : ℕ) : positiveCount b (2*k) = k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ,positiveCount_two,ih]; omega

theorem positiveCount_odd (b : Bool) (k : ℕ) :
    positiveCount b (2*k+1) = (if b = true then 1 else 0)+k := by
  rw [positiveCount_succ,positiveCount_even]

theorem card_alternating_pos (b : Bool) (l : ℕ) :
    Fintype.card {i // alternating b l i = true} = positiveCount b l := by
  classical
  rw [Fintype.card_subtype,Finset.card_filter]
  rfl

theorem card_alternating_neg (b : Bool) (l : ℕ) :
    Fintype.card {i // alternating b l i = false} = l-positiveCount b l := by
  classical
  have hh := Fintype.card_subtype_compl (fun i : Fin l => alternating b l i = true)
  simpa only [Bool.not_eq_true,Fintype.card_fin,card_alternating_pos] using hh

theorem alternating_charge (b : Bool) (l : ℕ) :
    (∑ i, boolSign (alternating b l i)) = 2*(positiveCount b l : ℤ)-l := by
  classical
  have hh (i : Fin l) : boolSign (alternating b l i) =
      2*(if alternating b l i = true then (1 : ℤ) else 0)-1 := by
    cases alternating b l i <;> norm_num
  simp only [hh,Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one,positiveCount]
  push_cast
  rfl

theorem card_pairColors_pos {I : Type uI} {J : Type uJ} [Fintype I] [Fintype J]
    (b : I → Bool) (c : J → Bool) :
    Fintype.card {i // pairColors b c i = true} =
      Fintype.card {i // b i = true} + Fintype.card {j // c j = false} := by
  classical
  simp only [Fintype.card_subtype,Finset.card_filter]
  rw [Fintype.sum_sum_type]
  simp only [pairColors,Sum.elim_inl,Sum.elim_inr,Bool.not_eq_true_eq_eq_false]
  rfl

theorem card_pairColors_neg {I : Type uI} {J : Type uJ} [Fintype I] [Fintype J]
    (b : I → Bool) (c : J → Bool) :
    Fintype.card {i // pairColors b c i = false} =
      Fintype.card {i // b i = false} + Fintype.card {j // c j = true} := by
  classical
  simp only [Fintype.card_subtype,Finset.card_filter]
  rw [Fintype.sum_sum_type]
  simp only [pairColors,Sum.elim_inl,Sum.elim_inr,Bool.not_eq_false_eq_eq_true]
  rfl

end RankTwo

def coefficientPair {G : Type uG} (h k : G →₀ ℝ) : ℝ := h.sum (fun g c => c * k g)

@[simp] theorem coefficientPair_self {G : Type uG} (h : G →₀ ℝ) :
    coefficientPair h h = coefficientSqNorm h := by
  unfold coefficientPair coefficientSqNorm
  apply Finsupp.sum_congr
  intro g _
  exact (pow_two (h g)).symm

@[simp] theorem coefficientPair_zero_left {G : Type uG} (k : G →₀ ℝ) : coefficientPair 0 k = 0 := by
  simp [coefficientPair]

@[simp] theorem coefficientPair_single_left {G : Type uG} (g : G) (c : ℝ) (k : G →₀ ℝ) :
    coefficientPair (Finsupp.single g c) k = c * k g := by simp [coefficientPair]

@[simp] theorem coefficientPair_add_left {G : Type uG} (h k l : G →₀ ℝ) :
    coefficientPair (h+k) l = coefficientPair h l + coefficientPair k l := by
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul ..)

@[simp] theorem coefficientPair_sum_left {I : Type uI} {G : Type uG} (s : Finset I) (h : I → G →₀ ℝ) (k : G →₀ ℝ) :
    coefficientPair (∑ i ∈ s, h i) k = ∑ i ∈ s, coefficientPair (h i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi,ih]

@[simp] theorem coefficientPair_zero_right {G : Type uG} (h : G →₀ ℝ) : coefficientPair h 0 = 0 := by
  simp [coefficientPair]

@[simp] theorem coefficientPair_add_right {G : Type uG} (h k l : G →₀ ℝ) :
    coefficientPair h (k+l) = coefficientPair h k + coefficientPair h l := by
  simp [coefficientPair,mul_add,Finsupp.sum_add]

@[simp] theorem coefficientPair_single_right {G : Type uG} (h : G →₀ ℝ) (g : G) (c : ℝ) :
    coefficientPair h (Finsupp.single g c) = h g * c := by
  classical
  simp [coefficientPair,Finsupp.sum,Finsupp.single_apply]
  exact fun h => Or.inl h

@[simp] theorem coefficientPair_sum_right {I : Type uI} {G : Type uG} (s : Finset I) (h : G →₀ ℝ) (k : I → G →₀ ℝ) :
    coefficientPair h (∑ i ∈ s, k i) = ∑ i ∈ s, coefficientPair h (k i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi,ih]

theorem coefficientPair_smul_left {G : Type uG} (c : ℝ) (h k : G →₀ ℝ) :
    coefficientPair (c • h) k = c * coefficientPair h k := by
  unfold coefficientPair
  rw [Finsupp.sum_smul_index (fun _ => zero_mul _)]
  simp only [mul_assoc,Finsupp.mul_sum]

theorem coefficientPair_smul_right {G : Type uG} (c : ℝ) (h k : G →₀ ℝ) :
    coefficientPair h (c • k) = c * coefficientPair h k := by
  unfold coefficientPair
  simp only [Finsupp.smul_apply,smul_eq_mul,Finsupp.mul_sum,mul_left_comm]

theorem coefficientPair_single_sums {I : Type uI} {J : Type uJ} {G : Type uG} (s : Finset I) (t : Finset J)
    (f : I → G) (g : J → G) (a : I → ℝ) (b : J → ℝ) :
    coefficientPair (∑ i ∈ s, Finsupp.single (f i) (a i)) (∑ j ∈ t, Finsupp.single (g j) (b j)) =
      ∑ i ∈ s, ∑ j ∈ t, if f i = g j then a i * b j else 0 := by
  classical
  rw [coefficientPair_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [coefficientPair_sum_right]
  simp only [coefficientPair_single_left,Finsupp.single_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : f i = g j
  · rw [ite_eq_left h.symm,ite_eq_left h]
  · rw [ite_eq_right (Ne.symm h),ite_eq_right h,mul_zero]

theorem coefficientPair_shells {I : Type uI} {J : Type uJ} {G : Type uG} (s : Finset I) (t : Finset J)
    (f : I → G) (g : J → G) :
    coefficientPair (∑ i ∈ s, Finsupp.single (f i) 1) (∑ j ∈ t, Finsupp.single (g j) 1) =
      ((s ×ˢ t).filter (fun p : I × J => f p.1 = g p.2)).card := by
  classical
  rw [coefficientPair_single_sums]
  simp only [mul_one,Finset.card_filter,Finset.sum_product]
  push_cast
  rfl

end FreeGroupFactorMain

end

end OAI
