import OAI.Geometry.Coboundary.Chambers
import OAI.Combinatorics.Coboundary.Joins

namespace OAI

/-!
Finite pivots, polynomial residue-chamber links, and exactness via finite joins.
-/

noncomputable section
open scoped Polynomial BigOperators

namespace CoboundaryExpanders.FinitePivots
open scoped BigOperators
variable {K : Type} [Field K] {N : ℕ}

def Leading (v : Fin N → K) (i : Fin N) : Prop :=
  v i ≠ 0 ∧ ∀ j, i < j → v j = 0

def HasPivot (W : Submodule K (Fin N → K)) (i : Fin N) : Prop :=
  ∃ v ∈ W, Leading v i

def prefSpace (K : Type) [Field K] (N k : ℕ) : Submodule K (Fin N → K) where
  carrier := {v | ∀ i, k ≤ i.val → v i = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i hi; simp [hx i hi,hy i hi]
  smul_mem' := by intro a x hx i hi; simp [hx i hi]

lemma exists_leading {v : Fin N → K} (hv : v ≠ 0) : ∃ i, Leading v i := by
  classical
  let s := Finset.univ.filter (fun i => v i ≠ 0)
  have hs : s.Nonempty := by
    by_contra hn
    apply hv
    ext i
    by_contra hi
    exact hn ⟨i,by simpa [s] using hi⟩
  refine ⟨s.max' hs,(Finset.mem_filter.mp (Finset.max'_mem s hs)).2,?_⟩
  intro j hj
  by_contra hz
  have hle := Finset.le_max' s j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩)
  exact (not_lt_of_ge hle) hj

lemma leading_single (i : Fin N) : Leading (Pi.single i (1 : K)) i := by
  classical
  simp only [Leading,Pi.single_eq_same,ne_eq,one_ne_zero,not_false_eq_true,true_and]
  intro j hj
  simpa only [Pi.single_apply] using (ite_eq_right (ne_of_gt hj) : (if j = i then (1 : K) else 0) = 0)

lemma eq_top_of_pivots (W : Submodule K (Fin N → K))
    (h : ∀ i, HasPivot W i) : W = ⊤ := by
  classical
  have hmem' : ∀ n, ∀ i : Fin N, i.val = n → Pi.single i (1 : K) ∈ W := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hei
      obtain ⟨v,hv,hvl⟩ := h i
      have hs : (∑ j ∈ Finset.univ.erase i, v j • Pi.single j (1 : K)) ∈ W := by
        apply W.sum_mem
        intro j hj
        have hji := (Finset.mem_erase.mp hj).1
        rcases lt_or_gt_of_ne hji with hlt | hgt
        · exact W.smul_mem _ (ih j.val (by omega) j rfl)
        · simp [hvl.2 j hgt]
      have he : v = (∑ j ∈ Finset.univ.erase i, v j • Pi.single j (1 : K)) +
          v i • Pi.single i (1 : K) := by
        rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]
        ext j
        simp [Finset.sum_apply,Pi.single_apply]
      have hh := W.sub_mem hv hs
      rw [show v - (∑ j ∈ Finset.univ.erase i, v j • Pi.single j (1 : K)) =
          v i • Pi.single i 1 by rw [sub_eq_iff_eq_add]; simpa [add_comm] using he] at hh
      have hh' := W.smul_mem (v i)⁻¹ hh
      rw [smul_smul,inv_mul_cancel₀ hvl.1,one_smul] at hh'
      exact hh'
  have hmem (i : Fin N) := hmem' i.val i rfl
  apply top_unique
  intro v _
  have he : v = ∑ i : Fin N, v i • Pi.single i (1 : K) := by
    ext j
    simp [Finset.sum_apply,Pi.single_apply]
  rw [he]
  exact W.sum_mem fun i _ => W.smul_mem _ (hmem i)

lemma disjoint_prefix_iff (W : Submodule K (Fin N → K)) (k : ℕ) :
    Disjoint W (prefSpace K N k) ↔ ∀ i, HasPivot W i → k ≤ i.val := by
  rw [Submodule.disjoint_def]
  constructor
  · intro h i ⟨v,hv,hvl⟩
    by_contra hn
    have hp : v ∈ prefSpace K N k := by
      intro j hj
      exact hvl.2 j (by change i.val < j.val; omega)
    have hz := h v hv hp
    exact hvl.1 (congr_fun hz i)
  · intro h v hv hp
    by_contra hz
    obtain ⟨i,hi⟩ := exists_leading hz
    have hh := h i ⟨v,hv,hi⟩
    exact hi.1 (hp i hh)

theorem isCompl_prefix_iff (W : Submodule K (Fin N → K)) (k : ℕ) :
    IsCompl W (prefSpace K N k) ↔ ∀ i, HasPivot W i ↔ k ≤ i.val := by
  classical
  constructor
  · intro h i
    refine ⟨(disjoint_prefix_iff W k).mp h.disjoint i,?_⟩
    intro hi
    have hm : Pi.single i (1 : K) ∈ W ⊔ prefSpace K N k := by rw [h.sup_eq_top]; trivial
    obtain ⟨w,hw,z,hz,he⟩ := Submodule.mem_sup.mp hm
    refine ⟨w,hw,?_,?_⟩
    · have hze := hz i hi
      have hei := congr_fun he i
      simp only [Pi.add_apply,Pi.single_eq_same,hze,add_zero] at hei
      exact hei ▸ one_ne_zero
    · intro j hj
      have hze := hz j (by change i.val < j.val at hj; omega)
      have hej := congr_fun he j
      simpa [hze,Pi.single_eq_of_ne (ne_of_gt hj)] using hej
  · intro h
    have hd := (disjoint_prefix_iff W k).mpr fun i hi => (h i).mp hi
    have ht : W ⊔ prefSpace K N k = ⊤ := by
      apply eq_top_of_pivots
      intro i
      by_cases hi : k ≤ i.val
      · obtain ⟨v,hv,hl⟩ := (h i).mpr hi
        exact ⟨v,(show W ≤ W ⊔ prefSpace K N k from le_sup_left) hv,hl⟩
      · refine ⟨Pi.single i 1,(show prefSpace K N k ≤ W ⊔ prefSpace K N k from le_sup_right) ?_,leading_single i⟩
        intro j hj
        have hji : j ≠ i := by intro he; subst j; omega
        simp [hji]
    exact ⟨hd, codisjoint_iff.mpr ht⟩

end CoboundaryExpanders.FinitePivots

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N M : ℕ}

lemma C_smul_vector (c : K) (v : V K N) : (Polynomial.C c) • v = c • v := by
  funext i
  exact (Polynomial.smul_eq_C_mul c).symm

def selectedSection (b : Fin N → V K N) (σ : Fin M → Fin N) :
    (Fin M → K) →ₗ[K] V K N where
  toFun x := ∑ r, x r • b (σ r)
  map_add' x y := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum,mul_smul]

lemma selectedSection_leading (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (hσ : StrictMono (fun r => N*a (σ r)+(σ r).val))
    (x : Fin M → K) (r : Fin M) (hx : FinitePivots.Leading x r) :
    Leading (selectedSection b σ x) (σ r) (a (σ r)) := by
  classical
  have hsec (i : Fin N) (e : ℕ) :
      ((selectedSection b σ x) i).coeff e = ∑ j, x j * (b (σ j) i).coeff e := by
    simp [selectedSection,Finset.sum_apply,Polynomial.finsetSum_coeff]
  constructor
  · rw [hsec,Finset.sum_eq_single r]
    · exact mul_ne_zero hx.1 (hb (σ r)).1
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with hlt | hgt
      · rw [(hb (σ j)).2 (σ r) (a (σ r)) (hσ hlt),mul_zero]
      · rw [hx.2 j hgt,zero_mul]
    · simp
  · intro i e he
    rw [hsec]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j ≤ r
    · rw [(hb (σ j)).2 i e ((hσ.monotone hj).trans_lt he),mul_zero]
    · rw [hx.2 j (lt_of_not_ge hj),zero_mul]

noncomputable def selectedResidue (b : Fin N → V K N) (σ : Fin M → Fin N)
    (D : Submodule K[X] (V K N)) : Submodule K (Fin M → K) :=
  (D.restrictScalars K).comap (selectedSection b σ)

lemma selectedSection_polynomial (b : Fin N → V K N) (σ : Fin M → Fin N) (x : Fin M → K) :
    selectedSection b σ x = ∑ r, Polynomial.C (x r) • b (σ r) := by
  simp only [selectedSection,LinearMap.coe_mk,AddHom.coe_mk,C_smul_vector]

lemma constant_remainder_mem_diagonal (b : Fin N → V K N) (s : Finset (Fin N))
    (f : Fin N → K[X]) :
    (∑ i, (f i - if i ∈ s then Polynomial.C ((f i).coeff 0) else 0) • b i) ∈
      diagonalModule b s := by
  classical
  apply Submodule.sum_mem
  intro i _
  by_cases hi : i ∈ s
  · simp only [ite_eq_left hi]
    have hd : Polynomial.X ∣ f i-Polynomial.C ((f i).coeff 0) := by
      apply Polynomial.X_dvd_iff.mpr
      simp
    obtain ⟨q,hq⟩ := hd
    rw [hq,mul_comm, mul_smul]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨i,by simp [diagonalFamily,hi]⟩
  · simp only [ite_eq_right hi,sub_zero]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨i,by simp [diagonalFamily,hi]⟩

lemma selectedSection_mem_of_combination (b : Fin N → V K N) (σ : Fin M → Fin N)
    (hσ : Function.Injective σ) (D : Submodule K[X] (V K N))
    (hCD : diagonalModule b (Finset.univ.image σ) ≤ D)
    (f : Fin N → K[X]) (hf : (∑ i, f i • b i) ∈ D) :
    selectedSection b σ (fun r => (f (σ r)).coeff 0) ∈ D := by
  classical
  let s := Finset.univ.image σ
  let g (i : Fin N) : K[X] := if i ∈ s then Polynomial.C ((f i).coeff 0) else 0
  have hg : (∑ i, g i • b i) = selectedSection b σ (fun r => (f (σ r)).coeff 0) := by
    rw [selectedSection_polynomial]
    calc
      (∑ i, g i • b i) = ∑ i ∈ s, Polynomial.C ((f i).coeff 0) • b i := by
        simp only [g,ite_smul,zero_smul,← Finset.sum_filter]
        simp
      _ = ∑ r, Polynomial.C ((f (σ r)).coeff 0) • b (σ r) := Finset.sum_image hσ.injOn
  have hc : (∑ i, (f i-g i) • b i) ∈ D := hCD (constant_remainder_mem_diagonal b s f)
  have hh := D.sub_mem hf hc
  have he : (∑ i, f i • b i) - (∑ i, (f i-g i) • b i) = ∑ i, g i • b i := by
    simp only [sub_smul,Finset.sum_sub_distrib,sub_sub_cancel]
  rw [he,hg] at hh
  exact hh

theorem selectedResidue_pivot_iff (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (hσ : StrictMono (fun r => N*a (σ r)+(σ r).val))
    (D : Submodule K[X] (V K N)) (hD : HasPivots D)
    (hCD : diagonalModule b (Finset.univ.image σ) ≤ D)
    (hDA : D ≤ Submodule.span K[X] (Set.range b)) (r : Fin M) :
    FinitePivots.HasPivot (selectedResidue b σ D) r ↔ pivotDegree D hD (σ r) = a (σ r) := by
  classical
  have hmon : a (σ r) ≤ pivotDegree D hD (σ r) := by
    have := pivotDegree_antitone (span_hasPivots b a hb) hD hDA (σ r)
    rwa [span_pivotDegree b a hb (σ r)] at this
  constructor
  · rintro ⟨x,hx,hxl⟩
    have hm : selectedSection b σ x ∈ D := hx
    exact le_antisymm (pivotDegree_min D hD (σ r) hm (selectedSection_leading b a hb σ hσ x r hxl)) hmon
  · intro he
    obtain ⟨f,hf⟩ := (Submodule.mem_span_range_iff_exists_fun K[X]).mp (hDA (pivot_mem D hD (σ r)))
    have hl : Leading (∑ i, f i • b i) (σ r) (a (σ r)) := by
      rw [hf,← he]
      exact pivot_leading D hD (σ r)
    obtain ⟨hfi,hdeg,hhigh⟩ := combination_lowest_pivot b a hb f (σ r) hl
    refine ⟨fun j => (f (σ j)).coeff 0,?_,?_,?_⟩
    · apply selectedSection_mem_of_combination b σ
        (fun i j hij => hσ.injective (congrArg (fun t => N*a t+t.val) hij)) D hCD f
      rw [hf]
      exact pivot_mem D hD (σ r)
    · intro hz
      dsimp only at hz
      apply hfi
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg,hz,Polynomial.C_0]
    · intro j hj
      dsimp only
      rw [hhigh (σ j) (hσ hj)]
      simp

theorem selectedResidue_opposed_iff (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (hσ : StrictMono (fun r => N*a (σ r)+(σ r).val))
    (D : Submodule K[X] (V K N)) (hD : HasPivots D)
    (hCD : diagonalModule b (Finset.univ.image σ) ≤ D)
    (hDA : D ≤ Submodule.span K[X] (Set.range b)) (k : ℕ) :
    IsCompl (selectedResidue b σ D) (FinitePivots.prefSpace K M k) ↔
      ∀ r, pivotDegree D hD (σ r) = a (σ r) ↔ k ≤ r.val := by
  rw [FinitePivots.isCompl_prefix_iff]
  simp only [selectedResidue_pivot_iff b a hb σ hσ D hD hCD hDA]

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N M : ℕ}

lemma X_smul_mem_diagonal (b : Fin N → V K N) (s : Finset (Fin N)) (v : V K N)
    (hv : v ∈ Submodule.span K[X] (Set.range b)) : (Polynomial.X : K[X]) • v ∈ diagonalModule b s := by
  classical
  obtain ⟨f,rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K[X]).mp hv
  rw [Finset.smul_sum]
  apply Submodule.sum_mem
  intro i _
  rw [smul_comm]
  apply Submodule.smul_mem
  by_cases hi : i ∈ s
  · exact Submodule.subset_span ⟨i,by simp [diagonalFamily,hi]⟩
  · apply Submodule.smul_mem
    exact Submodule.subset_span ⟨i,by simp [diagonalFamily,hi]⟩

lemma selectedSection_mem_span (b : Fin N → V K N) (σ : Fin M → Fin N) (x : Fin M → K) :
    selectedSection b σ x ∈ Submodule.span K[X] (Set.range b) := by
  rw [selectedSection_polynomial]
  apply Submodule.sum_mem
  intro r _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ r,rfl⟩)

lemma selectedSection_injective (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (hσ : StrictMono (fun r => N*a (σ r)+(σ r).val)) : Function.Injective (selectedSection b σ) := by
  apply (selectedSection b σ).ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  by_contra hn
  obtain ⟨r,hr⟩ := FinitePivots.exists_leading hn
  exact leading_ne_zero (selectedSection_leading b a hb σ hσ x r hr) hx

lemma selectedSection_mem_diagonal_iff (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (hσ : StrictMono (fun r => N*a (σ r)+(σ r).val)) (x : Fin M → K) :
    selectedSection b σ x ∈ diagonalModule b (Finset.univ.image σ) ↔ x = 0 := by
  classical
  constructor
  · intro hx
    by_contra hn
    obtain ⟨r,hr⟩ := FinitePivots.exists_leading hn
    have hl := selectedSection_leading b a hb σ hσ x r hr
    have hh := pivotDegree_min _ (diagonal_hasPivots b a hb (Finset.univ.image σ)) (σ r) hx hl
    rw [diagonal_pivotDegree b a hb] at hh
    have hm : σ r ∈ Finset.univ.image σ := Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩
    simp only [ite_eq_left hm] at hh
    omega
  · rintro rfl
    rw [map_zero]
    exact Submodule.zero_mem _

lemma combination_sub_selected_mem (b : Fin N → V K N) (σ : Fin M → Fin N)
    (hσ : Function.Injective σ) (f : Fin N → K[X]) :
    (∑ i, f i • b i) - selectedSection b σ (fun r => (f (σ r)).coeff 0) ∈
      diagonalModule b (Finset.univ.image σ) := by
  classical
  let s := Finset.univ.image σ
  let g (i : Fin N) : K[X] := if i ∈ s then Polynomial.C ((f i).coeff 0) else 0
  have hg : (∑ i, g i • b i) = selectedSection b σ (fun r => (f (σ r)).coeff 0) := by
    rw [selectedSection_polynomial]
    calc
      (∑ i, g i • b i) = ∑ i ∈ s, Polynomial.C ((f i).coeff 0) • b i := by
        simp only [g,ite_smul,zero_smul,← Finset.sum_filter]
        simp
      _ = ∑ r, Polynomial.C ((f (σ r)).coeff 0) • b (σ r) := Finset.sum_image hσ.injOn
  rw [← hg,← Finset.sum_sub_distrib]
  simp only [← sub_smul]
  exact constant_remainder_mem_diagonal b s f

lemma polynomial_smul_section_mod (b : Fin N → V K N) (σ : Fin M → Fin N)
    (f : K[X]) (x : Fin M → K) :
    f • selectedSection b σ x - selectedSection b σ (f.coeff 0 • x) ∈
      diagonalModule b (Finset.univ.image σ) := by
  have hd : Polynomial.X ∣ f-Polynomial.C (f.coeff 0) := Polynomial.X_dvd_iff.mpr (by simp)
  obtain ⟨q,hq⟩ := hd
  have he : f • selectedSection b σ x - selectedSection b σ (f.coeff 0 • x) =
      q • ((Polynomial.X : K[X]) • selectedSection b σ x) := by
    rw [map_smul,← C_smul_vector,← sub_smul,hq,mul_comm,mul_smul]
  rw [he]
  apply Submodule.smul_mem
  exact X_smul_mem_diagonal b _ _ (selectedSection_mem_span b σ x)

noncomputable def liftSelected (b : Fin N → V K N) (σ : Fin M → Fin N)
    (W : Submodule K (Fin M → K)) : Submodule K[X] (V K N) where
  carrier := {v | ∃ c ∈ diagonalModule b (Finset.univ.image σ), ∃ x ∈ W, v = c+selectedSection b σ x}
  zero_mem' := ⟨0,Submodule.zero_mem _,0,W.zero_mem,by simp⟩
  add_mem' := by
    rintro v w ⟨c,hc,x,hx,rfl⟩ ⟨d,hd,y,hy,rfl⟩
    refine ⟨c+d,Submodule.add_mem _ hc hd,x+y,W.add_mem hx hy,?_⟩
    rw [map_add]
    abel
  smul_mem' := by
    rintro f v ⟨c,hc,x,hx,rfl⟩
    refine ⟨f • c + (f • selectedSection b σ x - selectedSection b σ (f.coeff 0 • x)),
      Submodule.add_mem _ (Submodule.smul_mem _ f hc) (polynomial_smul_section_mod b σ f x),
      f.coeff 0 • x,W.smul_mem _ hx,?_⟩
    rw [smul_add]
    abel

lemma diagonal_le_liftSelected (b : Fin N → V K N) (σ : Fin M → Fin N)
    (W : Submodule K (Fin M → K)) : diagonalModule b (Finset.univ.image σ) ≤ liftSelected b σ W := by
  intro v hv
  exact ⟨v,hv,0,W.zero_mem,by simp⟩

lemma liftSelected_le_span (b : Fin N → V K N) (σ : Fin M → Fin N)
    (W : Submodule K (Fin M → K)) : liftSelected b σ W ≤ Submodule.span K[X] (Set.range b) := by
  rintro v ⟨c,hc,x,hx,rfl⟩
  exact Submodule.add_mem _ (diagonal_le_span b _ hc) (selectedSection_mem_span b σ x)

lemma selectedResidue_liftSelected (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (hσ : StrictMono (fun r => N*a (σ r)+(σ r).val)) (W : Submodule K (Fin M → K)) :
    selectedResidue b σ (liftSelected b σ W) = W := by
  ext x
  constructor
  · rintro ⟨c,hc,y,hy,he⟩
    have hh : selectedSection b σ (x-y) = c := by rw [map_sub,he]; abel
    have hz := (selectedSection_mem_diagonal_iff b a hb σ hσ (x-y)).mp (hh ▸ hc)
    have hxy := sub_eq_zero.mp hz
    exact hxy ▸ hy
  · intro hx
    exact ⟨0,Submodule.zero_mem _,x,hx,by simp⟩

lemma liftSelected_selectedResidue (b : Fin N → V K N) (σ : Fin M → Fin N)
    (hσ : Function.Injective σ) (D : Submodule K[X] (V K N))
    (hCD : diagonalModule b (Finset.univ.image σ) ≤ D)
    (hDA : D ≤ Submodule.span K[X] (Set.range b)) :
    liftSelected b σ (selectedResidue b σ D) = D := by
  apply le_antisymm
  · rintro v ⟨c,hc,x,hx,rfl⟩
    exact D.add_mem (hCD hc) hx
  · intro v hv
    obtain ⟨f,hf⟩ := (Submodule.mem_span_range_iff_exists_fun K[X]).mp (hDA hv)
    let x := fun r => (f (σ r)).coeff 0
    refine ⟨v-selectedSection b σ x,?_,x,?_,by abel⟩
    · rw [← hf]
      exact combination_sub_selected_mem b σ hσ f
    · exact selectedSection_mem_of_combination b σ hσ D hCD f (hf ▸ hv)

noncomputable def selectedIntervalEquiv (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (hσ : StrictMono (fun r => N*a (σ r)+(σ r).val)) :
    {D : Submodule K[X] (V K N) // diagonalModule b (Finset.univ.image σ) ≤ D ∧
      D ≤ Submodule.span K[X] (Set.range b)} ≃o Submodule K (Fin M → K) where
  toFun D := selectedResidue b σ D.val
  invFun W := ⟨liftSelected b σ W,diagonal_le_liftSelected b σ W,liftSelected_le_span b σ W⟩
  left_inv D := Subtype.ext (liftSelected_selectedResidue b σ
    (fun i j he => hσ.injective (congrArg (fun t => N*a t+t.val) he)) D.val D.property.1 D.property.2)
  right_inv W := selectedResidue_liftSelected b a hb σ hσ W
  map_rel_iff' := by
    intro D E
    constructor
    · intro h
      change D.val ≤ E.val
      rw [← liftSelected_selectedResidue b σ
        (fun i j he => hσ.injective (congrArg (fun t => N*a t+t.val) he)) D.val D.property.1 D.property.2]
      rintro v ⟨c,hc,x,hx,rfl⟩
      exact E.val.add_mem (E.property.1 hc) (h hx)
    · intro h x hx
      exact h hx

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.FinitePivots
open Module
variable {K : Type} [Field K] {N : ℕ}

noncomputable def prefEquiv (k : ℕ) (hk : k ≤ N) :
    (Fin k → K) ≃ₗ[K] prefSpace K N k where
  toFun x := ⟨fun i => if h : i.val < k then x ⟨i.val,h⟩ else 0, by
    intro i hi
    simp [show ¬i.val < k from by omega]⟩
  invFun y := fun i => y.val ⟨i.val,lt_of_lt_of_le i.isLt hk⟩
  left_inv x := by funext i; simp
  right_inv y := by
    apply Subtype.ext
    funext i
    dsimp only
    split_ifs with hi
    · rfl
    · exact (y.property i (by omega)).symm
  map_add' x y := by
    apply Subtype.ext
    funext i
    change (if h : i.val < k then (x+y) ⟨i.val,h⟩ else 0) =
      (if h : i.val < k then x ⟨i.val,h⟩ else 0) + (if h : i.val < k then y ⟨i.val,h⟩ else 0)
    split_ifs <;> simp_all
  map_smul' c x := by
    apply Subtype.ext
    funext i
    change (if h : i.val < k then (c • x) ⟨i.val,h⟩ else 0) =
      c • (if h : i.val < k then x ⟨i.val,h⟩ else 0)
    split_ifs <;> simp_all

lemma prefSpace_finrank (k : ℕ) (hk : k ≤ N) : finrank K (prefSpace K N k) = k := by
  rw [← (prefEquiv (K := K) k hk).finrank_eq]
  simp

noncomputable def prefixFlag (K : Type) [Field K] (N : ℕ) :
    SphericalOpposition.CompleteFlag K (Fin N → K) N where
  space i := prefSpace K N i.val
  mono := by intro i j hij v hv l hl; exact hv l (le_trans hij hl)
  dimension := by simp
  rank i := prefSpace_finrank i.val (by omega)

lemma prefixFlag_opposed_iff (W : Submodule K (Fin N → K)) :
    (prefixFlag K N).Opposed W ↔ ∀ i, HasPivot W i ↔ N-finrank K W ≤ i.val := by
  exact isCompl_prefix_iff W _

end CoboundaryExpanders.FinitePivots

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
open Module InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
variable {K : Type} [Field K] {N M : ℕ}

abbrev SelectedInterval (b : Fin N → V K N) (σ : Fin M → Fin N) :=
  {D : Submodule K[X] (V K N) // diagonalModule b (Finset.univ.image σ) ≤ D ∧
    D ≤ Submodule.span K[X] (Set.range b)}

lemma selectedInterval_hasPivots (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N) (D : SelectedInterval b σ) :
    HasPivots D.val := by
  intro i
  obtain ⟨m,v,hv,hl⟩ := diagonal_hasPivots b a hb (Finset.univ.image σ) i
  exact ⟨m,v,D.property.1 hv,hl⟩

def PrefixPattern (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N) (D : SelectedInterval b σ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ k < M ∧ ∀ r,
    pivotDegree D.val (selectedInterval_hasPivots b a hb σ D) (σ r) = a (σ r) ↔ k ≤ r.val

lemma prefixPattern_iff_good (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (hσ : StrictMono (fun r => N*a (σ r)+(σ r).val)) (D : SelectedInterval b σ) :
    PrefixPattern b a hb σ D ↔
      (FinitePivots.prefixFlag K M).Good (selectedIntervalEquiv b a hb σ hσ D) := by
  let W := selectedResidue b σ D.val
  have hop (k : ℕ) := selectedResidue_opposed_iff b a hb σ hσ D.val
    (selectedInterval_hasPivots b a hb σ D) D.property.1 D.property.2 k
  change PrefixPattern b a hb σ D ↔ 0 < finrank K W ∧ finrank K W < M ∧
    IsCompl W (FinitePivots.prefSpace K M (M-finrank K W))
  constructor
  · rintro ⟨k,hk,hkM,hpat⟩
    have hc := (hop k).mpr hpat
    have hr := Submodule.finrank_add_eq_of_isCompl hc
    rw [FinitePivots.prefSpace_finrank k hkM.le] at hr
    simp only [Module.finrank_pi,Fintype.card_fin] at hr
    have hdim : finrank K W + k = M := hr
    have he : M-finrank K W = k := by omega
    exact ⟨by omega,by omega,he ▸ hc⟩
  · rintro ⟨hpos,hlt,hc⟩
    refine ⟨M-finrank K W,by omega,by omega,(hop _).mp hc⟩

def prefixPatternComplex (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N) :
    InfiniteChains.Complex (SelectedInterval b σ) where
  faces := {s | (∀ D ∈ s, PrefixPattern b a hb σ D) ∧
    (s : Set (SelectedInterval b σ)).Pairwise (fun D E => D ≤ E ∨ E ≤ D)}
  empty_mem := by simp
  downward := by intro s t hs hts; exact ⟨fun D hD => hs.1 D (hts hD),hs.2.mono hts⟩

lemma prefixPattern_faces_equiv (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (hσ : StrictMono (fun r => N*a (σ r)+(σ r).val)) (s : Finset (SelectedInterval b σ)) :
    s ∈ (prefixPatternComplex b a hb σ).faces ↔
      s.image (selectedIntervalEquiv b a hb σ hσ) ∈ (FinitePivots.prefixFlag K M).complex.faces := by
  classical
  let e := selectedIntervalEquiv b a hb σ hσ
  constructor
  · intro hs
    constructor
    · rintro W hW
      obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hW
      exact (prefixPattern_iff_good b a hb σ hσ D).mp (hs.1 D hD)
    · intro W hW Z hZ hne
      obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hW
      obtain ⟨E,hE,rfl⟩ := Finset.mem_image.mp hZ
      rcases hs.2 hD hE (fun h => hne (congrArg e h)) with h | h
      · exact Or.inl (e.monotone h)
      · exact Or.inr (e.monotone h)
  · intro hs
    constructor
    · intro D hD
      exact (prefixPattern_iff_good b a hb σ hσ D).mpr
        (hs.1 (e D) (Finset.mem_image.mpr ⟨D,hD,rfl⟩))
    · intro D hD E hE hne
      have h := hs.2 (Finset.mem_image.mpr ⟨D,hD,rfl⟩)
        (Finset.mem_image.mpr ⟨E,hE,rfl⟩) (fun h => hne (e.injective h))
      exact h.imp e.le_iff_le.mp e.le_iff_le.mp

theorem uniform_polynomial_residue_exactness (r : ℕ) :
    ∃ Q : ℕ, ∀ (K : Type) [Field K] [Fintype K] (N M : ℕ)
      (b : Fin N → V K N) (a : Fin N → ℕ) (hb : ∀ i, Leading (b i) i (a i))
      (σ : Fin M → Fin N), StrictMono (fun i => N*a (σ i)+(σ i).val) →
      r+2 ≤ M → Q < Fintype.card K →
        ExactIn (prefixPatternComplex b a hb σ).faces r := by
  classical
  obtain ⟨Q,hQ⟩ := SphericalOpposition.CompleteFlag.uniform_spherical_exactness r
  refine ⟨Q,?_⟩
  intro K _ _ N M b a hb σ hσ hM hcard
  exact exactIn_equivalence (selectedIntervalEquiv b a hb σ hσ).toEquiv _ _
    (prefixPattern_faces_equiv b a hb σ hσ) r
    (hQ K (Fin M → K) M (FinitePivots.prefixFlag K M) hM hcard r le_rfl)

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N M : ℕ}

noncomputable def selectedIncrements (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (D : SelectedInterval b σ) : Finset (Fin M) :=
  Finset.univ.filter fun r => a (σ r) < pivotDegree D.val (selectedInterval_hasPivots b a hb σ D) (σ r)

lemma selected_pivot_bounds (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (D : SelectedInterval b σ) (i : Fin N) :
    a i ≤ pivotDegree D.val (selectedInterval_hasPivots b a hb σ D) i ∧
      pivotDegree D.val (selectedInterval_hasPivots b a hb σ D) i ≤
        a i + if i ∈ Finset.univ.image σ then 1 else 0 := by
  constructor
  · have h := pivotDegree_antitone (span_hasPivots b a hb)
      (selectedInterval_hasPivots b a hb σ D) D.property.2 i
    rwa [span_pivotDegree b a hb i] at h
  · have h := pivotDegree_antitone (selectedInterval_hasPivots b a hb σ D)
      (diagonal_hasPivots b a hb (Finset.univ.image σ)) D.property.1 i
    rwa [diagonal_pivotDegree b a hb (Finset.univ.image σ) i] at h

lemma selectedIncrements_mono (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N) :
    Antitone (selectedIncrements b a hb σ) := by
  classical
  intro D E hDE r hr
  simp only [selectedIncrements,Finset.mem_filter,Finset.mem_univ,true_and] at hr ⊢
  exact hr.trans_le (pivotDegree_antitone (selectedInterval_hasPivots b a hb σ E)
    (selectedInterval_hasPivots b a hb σ D) hDE (σ r))

lemma selectedIncrements_strict (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N) :
    StrictAnti (selectedIncrements b a hb σ) := by
  classical
  intro D E hDE
  apply lt_of_le_of_ne (selectedIncrements_mono b a hb σ hDE.le)
  intro he
  have hEq : E.val = D.val := by
    apply eq_of_le_same_pivots (selectedInterval_hasPivots b a hb σ E)
      (selectedInterval_hasPivots b a hb σ D) hDE.le
    intro i
    have hD := selected_pivot_bounds b a hb σ D i
    have hE := selected_pivot_bounds b a hb σ E i
    by_cases hi : i ∈ Finset.univ.image σ
    · obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hi
      have hh := Finset.ext_iff.mp he r
      simp only [selectedIncrements,Finset.mem_filter,Finset.mem_univ,true_and] at hh
      simp only [Finset.mem_image,exists_apply_eq_apply,Finset.mem_univ,true_and,ite_true] at hD hE
      omega
    · simp only [hi,ite_false,Nat.add_zero] at hD hE
      omega
  exact hDE.ne (Subtype.ext hEq.symm)

lemma full_chain_card {L : ℕ} (S : Fin (L+1) → Finset (Fin L)) (hS : StrictMono S)
    (r : Fin (L+1)) : (S r).card = r.val := by
  let f (r : Fin (L+1)) : Fin (L+1) := ⟨(S r).card,
    Nat.lt_succ_of_le (by simpa using Finset.card_le_card (Finset.subset_univ (S r)))⟩
  have hf : StrictMono f := fun r s hrs => Finset.card_lt_card (hS hrs)
  exact congrArg Fin.val (congr_fun hf.eq_id r)

theorem selected_flag_permutation (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (F : Fin (M+1) → SelectedInterval b σ) (hF : StrictAnti F) :
    ∃ π : Equiv.Perm (Fin M), ∀ r : Fin M,
      selectedIncrements b a hb σ (F r.succ) =
        insert (π r) (selectedIncrements b a hb σ (F r.castSucc)) ∧
      π r ∉ selectedIncrements b a hb σ (F r.castSucc) :=
  full_chain_permutation _ ((selectedIncrements_strict b a hb σ).comp hF)

lemma selectedIncrements_card (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (F : Fin (M+1) → SelectedInterval b σ) (hF : StrictAnti F) (r : Fin (M+1)) :
    (selectedIncrements b a hb σ (F r)).card = r.val :=
  full_chain_card _ ((selectedIncrements_strict b a hb σ).comp hF) r

lemma selectedIncrements_prefix_iff (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (D : SelectedInterval b σ) (k : ℕ) :
    selectedIncrements b a hb σ D = Finset.univ.filter (fun r => r.val < k) ↔
      ∀ r, pivotDegree D.val (selectedInterval_hasPivots b a hb σ D) (σ r) = a (σ r) ↔ k ≤ r.val := by
  classical
  rw [Finset.ext_iff]
  simp only [selectedIncrements,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor <;> intro h r
  · have hh := h r
    have hlo := (selected_pivot_bounds b a hb σ D (σ r)).1
    omega
  · have hh := h r
    have hlo := (selected_pivot_bounds b a hb σ D (σ r)).1
    omega

lemma fin_prefix_card {L k : ℕ} (hk : k ≤ L) :
    (Finset.univ.filter (fun r : Fin L => r.val < k)).card = k := by
  classical
  let e : {r : Fin L // r.val < k} ≃ Fin k :=
    { toFun := fun r => ⟨r.val.val,r.property⟩
      invFun := fun r => ⟨⟨r.val,lt_of_lt_of_le r.isLt hk⟩,r.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_subtype _).symm.trans ((Fintype.card_congr e).trans (Fintype.card_fin k))

theorem selected_flag_good_iff (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (F : Fin (M+1) → SelectedInterval b σ) (hF : StrictAnti F) :
    (∀ r : Fin (M+1), 0 < r.val → r.val < M → PrefixPattern b a hb σ (F r)) ↔
      ∀ r : Fin (M+1), selectedIncrements b a hb σ (F r) =
        Finset.univ.filter (fun i => i.val < r.val) := by
  classical
  constructor
  · intro h r
    by_cases hzero : r.val = 0
    · have hh := selectedIncrements_card b a hb σ F hF r
      rw [hzero] at hh
      rw [Finset.card_eq_zero.mp hh]
      simp [hzero]
    · by_cases hlast : r.val = M
      · have hh := selectedIncrements_card b a hb σ F hF r
        have he : selectedIncrements b a hb σ (F r) = Finset.univ :=
          Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simpa [hlast] using hh.ge)
        rw [he]; simp [hlast]
      · obtain ⟨k,hk,hkM,hpat⟩ := h r (by omega) (by omega)
        have he := (selectedIncrements_prefix_iff b a hb σ (F r) k).mpr hpat
        have hc := selectedIncrements_card b a hb σ F hF r
        rw [he,fin_prefix_card hkM.le] at hc
        rwa [hc] at he
  · intro h r hr hrM
    exact ⟨r.val,hr,hrM,(selectedIncrements_prefix_iff b a hb σ (F r) r.val).mp (h r)⟩

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
open AffineWindow
variable {K : Type} [Field K] {N M : ℕ}

lemma full_word_refl_iff {L : ℕ} (S : Fin (L+1) → Finset (Fin L))
    (hS : StrictMono S) (π : Equiv.Perm (Fin L))
    (hπ : ∀ r : Fin L, S r.succ = insert (π r) (S r.castSucc) ∧ π r ∉ S r.castSucc) :
    π = Equiv.refl _ ↔ ∀ r : Fin (L+1), S r = Finset.univ.filter (fun i => i.val < r.val) := by
  classical
  constructor
  · intro he r
    subst π
    induction r using Fin.induction with
    | zero =>
      have hh := full_chain_card S hS 0
      rw [Fin.val_zero] at hh
      rw [Finset.card_eq_zero.mp hh]
      simp
    | succ r ih =>
      rw [(hπ r).1,ih]
      ext i
      simp only [Finset.mem_insert,Equiv.refl_apply,Finset.mem_filter,Finset.mem_univ,
        true_and,Fin.val_succ,Fin.val_castSucc]
      constructor
      · rintro (rfl|hi) <;> omega
      · intro hi
        by_cases he : i = r
        · exact Or.inl he
        · have hn : i.val ≠ r.val := fun h => he (Fin.ext h)
          exact Or.inr (by omega)
  · intro h
    apply Equiv.ext
    intro r
    have hm : π r ∈ S r.succ := by rw [(hπ r).1]; simp
    have hn := (hπ r).2
    rw [h r.succ] at hm
    rw [h r.castSucc] at hn
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Fin.val_succ,Fin.val_castSucc,not_lt] at hm hn
    apply Fin.ext
    change (π r).val = r.val
    omega

noncomputable def selectedWord (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (F : Fin (M+1) → SelectedInterval b σ) (hF : StrictAnti F) : Equiv.Perm (Fin M) :=
  (selected_flag_permutation b a hb σ F hF).choose

lemma selectedWord_spec (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (F : Fin (M+1) → SelectedInterval b σ) (hF : StrictAnti F) (r : Fin M) :
    selectedIncrements b a hb σ (F r.succ) =
      insert (selectedWord b a hb σ F hF r) (selectedIncrements b a hb σ (F r.castSucc)) ∧
    selectedWord b a hb σ F hF r ∉ selectedIncrements b a hb σ (F r.castSucc) :=
  (selected_flag_permutation b a hb σ F hF).choose_spec r

lemma selectedWord_refl_iff (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (F : Fin (M+1) → SelectedInterval b σ) (hF : StrictAnti F) :
    selectedWord b a hb σ F hF = Equiv.refl _ ↔
      ∀ r : Fin (M+1), 0 < r.val → r.val < M → PrefixPattern b a hb σ (F r) := by
  rw [full_word_refl_iff _ ((selectedIncrements_strict b a hb σ).comp hF) _
    (selectedWord_spec b a hb σ F hF)]
  exact (selected_flag_good_iff b a hb σ F hF).symm

def pivotWeight (a : Fin N → ℕ) (σ : Fin M → Fin N) (r : Fin M) : ℤ :=
  N*a (σ r) + (σ r).val

lemma pivotWeight_mod (a : Fin N → ℕ) (σ : Fin M → Fin N) (r : Fin M) :
    pivotWeight a σ r % (N : ℤ) = (σ r).val := by
  unfold pivotWeight
  have hh : 0 ≤ ((σ r).val : ℤ) := Int.natCast_nonneg _
  have ht : ((σ r).val : ℤ) < N := by exact_mod_cast (σ r).isLt
  simp only [Int.add_emod,Int.mul_emod_right,Int.zero_add,
    Int.emod_eq_of_lt hh ht]

lemma pivotWeight_strict (a : Fin N → ℕ) (σ : Fin M → Fin N)
    (hσ : StrictMono (fun r => N*a (σ r)+(σ r).val)) : StrictMono (pivotWeight a σ) := by
  intro r s hrs
  have hh := hσ hrs
  dsimp only [pivotWeight]
  exact_mod_cast hh

lemma pivotWeight_residues (a : Fin N → ℕ) (σ : Fin M → Fin N)
    (hσ : StrictMono (fun r => N*a (σ r)+(σ r).val)) :
    Function.Injective (fun r => pivotWeight a σ r % (N : ℤ)) := by
  intro r s he
  dsimp only at he
  rw [pivotWeight_mod,pivotWeight_mod] at he
  have hh : σ r = σ s := Fin.ext (by exact_mod_cast he)
  apply hσ.injective
  dsimp only
  rw [hh]

theorem selected_refinement_length (hN : 0 < N)
    (b : Fin N → V K N) (a : Fin N → ℕ) (hb : ∀ i, Leading (b i) i (a i))
    (σ : Fin M → Fin N) (hσ : StrictMono (fun r => N*a (σ r)+(σ r).val))
    (F : Fin (M+1) → SelectedInterval b σ) (hF : StrictAnti F) (l r : List ℤ) :
    inversion (N := N) (l ++ List.ofFn (pivotWeight a σ ∘ selectedWord b a hb σ F hF) ++ r) =
      inversion (N := N) (l ++ List.ofFn (pivotWeight a σ) ++ r) +
        pairs disorder (List.ofFn (pivotWeight a σ ∘ selectedWord b a hb σ F hF)) := by
  apply inversion_sorted_middle hN
    l r ((selectedWord b a hb σ F hF).ofFn_comp_perm _).symm
  · exact List.pairwise_ofFn.mpr fun _ _ h => ((pivotWeight_strict a σ hσ) h).le
  · apply List.pairwise_ofFn.mpr
    intro i j hij he
    exact (ne_of_lt hij) ((selectedWord b a hb σ F hF).injective ((pivotWeight_residues a σ hσ) he))

theorem selected_refinement_minimum_iff (hN : 0 < N)
    (b : Fin N → V K N) (a : Fin N → ℕ) (hb : ∀ i, Leading (b i) i (a i))
    (σ : Fin M → Fin N) (hσ : StrictMono (fun r => N*a (σ r)+(σ r).val))
    (F : Fin (M+1) → SelectedInterval b σ) (hF : StrictAnti F) (l r : List ℤ) :
    inversion (N := N) (l ++ List.ofFn (pivotWeight a σ ∘ selectedWord b a hb σ F hF) ++ r) =
      inversion (N := N) (l ++ List.ofFn (pivotWeight a σ) ++ r) ↔
      ∀ t : Fin (M+1), 0 < t.val → t.val < M → PrefixPattern b a hb σ (F t) := by
  rw [← selectedWord_refl_iff b a hb σ F hF]
  constructor
  · intro he
    have hlen := selected_refinement_length hN b a hb σ hσ F hF l r
    have hz : pairs disorder (List.ofFn (pivotWeight a σ ∘ selectedWord b a hb σ F hF)) = 0 := by omega
    have hs := (disorder_zero_iff _).mp hz
    have hi := List.pairwise_ofFn.mpr (fun _ _ h => ((pivotWeight_strict a σ hσ) h).le)
    have hl := ((selectedWord b a hb σ F hF).ofFn_comp_perm (pivotWeight a σ)).eq_of_pairwise' hs hi
    apply Equiv.ext
    intro i
    exact (pivotWeight_strict a σ hσ).injective
      (congr_fun (List.ofFn_inj.mp hl) i)
  · intro he
    simp only [he,Equiv.refl_apply,Function.comp_def]

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
open Module InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
variable {K : Type} [Field K] {N M : ℕ}

theorem prefix_face_complete_refinement
    (b : Fin N → V K N) (a : Fin N → ℕ) (hb : ∀ i, Leading (b i) i (a i))
    (σ : Fin M → Fin N) (hσ : StrictMono (fun r => N*a (σ r)+(σ r).val))
    (s : Finset (SelectedInterval b σ)) (hs : s ∈ (prefixPatternComplex b a hb σ).faces) :
    ∃ F : Fin (M+1) → SelectedInterval b σ, StrictAnti F ∧
      (∀ r : Fin (M+1), 0 < r.val → r.val < M → PrefixPattern b a hb σ (F r)) ∧
      ∀ D ∈ s, ∃ r : Fin (M+1), 0 < r.val ∧ r.val < M ∧ F r = D := by
  classical
  let e := selectedIntervalEquiv b a hb σ hσ
  let P := FinitePivots.prefixFlag K M
  have hs' : s.image e ∈ P.complex.faces := (prefixPattern_faces_equiv b a hb σ hσ s).mp hs
  obtain ⟨t,ht,hst⟩ := P.exists_full_face (s.image e) hs'
  obtain ⟨E,hE,hEt⟩ := P.exists_flag_from_face t ht
  let F (r : Fin (M+1)) : SelectedInterval b σ := e.symm (E.space r.rev)
  have hEstr : StrictMono E.space := by
    intro i j hij
    apply lt_of_le_of_ne (E.mono hij.le)
    intro he
    have hh := congrArg (fun W : Submodule K (Fin M → K) => Module.finrank K W) he
    rw [E.rank,E.rank] at hh
    exact (ne_of_lt hij) (Fin.ext hh)
  have hF : StrictAnti F := by
    intro i j hij
    exact e.symm.strictMono (hEstr (Fin.rev_lt_rev.mpr hij))
  have hgood (r : Fin (M+1)) (hr0 : 0 < r.val) (hrM : r.val < M) : PrefixPattern b a hb σ (F r) := by
    apply (prefixPattern_iff_good b a hb σ hσ (F r)).mpr
    change P.Good (e (e.symm (E.space r.rev)))
    rw [e.apply_symm_apply]
    refine ⟨?_,?_,?_⟩
    · rw [E.rank]
      simp only [Fin.val_rev]
      omega
    · rw [E.rank]
      simp only [Fin.val_rev]
      omega
    · change IsCompl (E.space r.rev) (P.space ⟨M-finrank K (E.space r.rev),_⟩)
      simpa only [E.rank] using (SphericalOpposition.CompleteFlag.opposite_symm hE) r.rev
  refine ⟨F,hF,hgood,?_⟩
  intro D hD
  obtain ⟨i,hi0,hiM,hi⟩ := (hEt (e D)).mp (hst (Finset.mem_image.mpr ⟨D,hD,rfl⟩))
  refine ⟨i.rev,?_,?_,?_⟩
  · simp only [Fin.val_rev]; omega
  · simp only [Fin.val_rev]; omega
  · change e.symm (E.space i.rev.rev) = D
    rw [Fin.rev_rev,hi,e.symm_apply_apply]

theorem prefix_face_iff_minimum_refinement (hN : 0 < N)
    (b : Fin N → V K N) (a : Fin N → ℕ) (hb : ∀ i, Leading (b i) i (a i))
    (σ : Fin M → Fin N) (hσ : StrictMono (fun r => N*a (σ r)+(σ r).val))
    (s : Finset (SelectedInterval b σ)) (l r : List ℤ) :
    s ∈ (prefixPatternComplex b a hb σ).faces ↔
      ∃ (F : Fin (M+1) → SelectedInterval b σ) (hF : StrictAnti F),
        AffineWindow.inversion (N := N)
          (l ++ List.ofFn (pivotWeight a σ ∘ selectedWord b a hb σ F hF) ++ r) =
        AffineWindow.inversion (N := N) (l ++ List.ofFn (pivotWeight a σ) ++ r) ∧
        ∀ D ∈ s, ∃ t : Fin (M+1), 0 < t.val ∧ t.val < M ∧ F t = D := by
  constructor
  · intro hs
    obtain ⟨F,hF,hgood,hmem⟩ := prefix_face_complete_refinement b a hb σ hσ s hs
    exact ⟨F,hF,(selected_refinement_minimum_iff hN b a hb σ hσ F hF l r).mpr hgood,hmem⟩
  · rintro ⟨F,hF,hmin,hmem⟩
    have hgood := (selected_refinement_minimum_iff hN b a hb σ hσ F hF l r).mp hmin
    refine ⟨?_,?_⟩
    · intro D hD
      obtain ⟨t,ht0,htM,rfl⟩ := hmem D hD
      exact hgood t ht0 htM
    · intro D hD E hE _
      obtain ⟨i,_,_,rfl⟩ := hmem D hD
      obtain ⟨j,_,_,rfl⟩ := hmem E hE
      rcases le_total i j with h | h
      · exact Or.inr (hF.antitone h)
      · exact Or.inl (hF.antitone h)

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}
lemma diagonalFamily_union (b : Fin N → V K N) (s t : Finset (Fin N))
    (h : Disjoint s t) : diagonalFamily (diagonalFamily b s) t = diagonalFamily b (s ∪ t) := by
  classical
  funext i
  have hh := Finset.disjoint_left.mp h
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all [diagonalFamily]
lemma diagonalModule_union (b : Fin N → V K N) (s t : Finset (Fin N))
    (h : Disjoint s t) : diagonalModule (diagonalFamily b s) t = diagonalModule b (s ∪ t) := by
  unfold diagonalModule
  rw [diagonalFamily_union b s t h]

noncomputable def wordSlice (π : Equiv.Perm (Fin N)) (a b : Fin (N+1)) : Fin (b.val-a.val) → Fin N :=
  fun r => π ⟨a.val+r.val,by have := r.isLt; have := b.isLt; omega⟩
lemma wordSlice_injective (π : Equiv.Perm (Fin N)) (a b : Fin (N+1)) :
    Function.Injective (wordSlice π a b) := by
  intro r s he
  have hv := congrArg Fin.val (π.injective he)
  apply Fin.ext
  dsimp only [wordSlice] at hv
  omega
lemma mem_wordSlice_image (π : Equiv.Perm (Fin N)) (a b : Fin (N+1)) (i : Fin N) :
    i ∈ Finset.univ.image (wordSlice π a b) ↔ a.val ≤ (π.symm i).val ∧ (π.symm i).val < b.val := by
  classical
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨r,rfl⟩
    simp only [wordSlice,Equiv.symm_apply_apply,Fin.val_mk]
    have := r.isLt
    omega
  · rintro ⟨ha,hb⟩
    refine ⟨⟨(π.symm i).val-a.val,by omega⟩,?_⟩
    change π ⟨a.val+((π.symm i).val-a.val),_⟩ = i
    have he : (⟨a.val+((π.symm i).val-a.val),by omega⟩ : Fin N) = π.symm i := Fin.ext (by dsimp only; omega)
    rw [he,Equiv.apply_symm_apply]
lemma wordPrefix_disjoint_slice (π : Equiv.Perm (Fin N)) (a b : Fin (N+1)) :
    Disjoint (wordPrefix π a) (Finset.univ.image (wordSlice π a b)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hs
  have hh := (mem_wordSlice_image π a b i).mp hs
  simp only [wordPrefix,Finset.mem_filter,Finset.mem_univ,true_and] at hi
  omega
lemma wordPrefix_union_slice (π : Equiv.Perm (Fin N)) (a b : Fin (N+1)) (hab : a ≤ b) :
    wordPrefix π a ∪ Finset.univ.image (wordSlice π a b) = wordPrefix π b := by
  classical
  ext i
  rw [Finset.mem_union,mem_wordSlice_image]
  simp only [wordPrefix,Finset.mem_filter,Finset.mem_univ,true_and]
  change a.val ≤ b.val at hab
  omega

namespace ResidueChamber
variable (C : ResidueChamber (K := K) (N := N))
noncomputable def blockBasis (b : Fin N → V K N) (a : Fin (N+1)) : Fin N → V K N :=
  diagonalFamily b (wordPrefix C.word a)
noncomputable def blockDegree (a : Fin (N+1)) (i : Fin N) : ℕ :=
  pivotDegree C.top C.hasTop i + if (C.word.symm i).val < a.val then 1 else 0
lemma blockBasis_leading (b : Fin N → V K N)
    (hb : ∀ i, Leading (b i) i (pivotDegree C.top C.hasTop i)) (a : Fin (N+1)) (i : Fin N) :
    Leading (C.blockBasis b a i) i (C.blockDegree a i) := by
  simpa only [blockBasis,blockDegree,wordPrefix,Finset.mem_filter,Finset.mem_univ,true_and] using
    diagonal_leading b _ hb (wordPrefix C.word a) i
lemma block_upper (b : Fin N → V K N)
    (hb : ∀ r, C.stage r = diagonalModule b (wordPrefix C.word r)) (a : Fin (N+1)) :
    Submodule.span K[X] (Set.range (C.blockBasis b a)) = C.stage a := (hb a).symm
lemma block_lower (b : Fin N → V K N)
    (hb : ∀ r, C.stage r = diagonalModule b (wordPrefix C.word r)) (a z : Fin (N+1)) (haz : a ≤ z) :
    diagonalModule (C.blockBasis b a) (Finset.univ.image (wordSlice C.word a z)) = C.stage z := by
  rw [blockBasis,diagonalModule_union b _ _ (wordPrefix_disjoint_slice C.word a z),
    wordPrefix_union_slice C.word a z haz,← hb z]
lemma block_weight (a z : Fin (N+1)) (r : Fin (z.val-a.val)) :
    (N*C.blockDegree a (wordSlice C.word a z r)+(wordSlice C.word a z r).val : ℕ) =
      N*pivotDegree C.top C.hasTop (C.word ⟨a.val+r.val,by have := r.isLt; have := z.isLt; omega⟩)+
        (C.word ⟨a.val+r.val,by have := r.isLt; have := z.isLt; omega⟩).val := by
  simp only [wordSlice,blockDegree,Equiv.symm_apply_apply,Fin.val_mk]
  rw [ite_eq_right (by omega),Nat.add_zero]
lemma sorted_block_selection (a z : Fin (N+1))
    (hs : (AffineWindow.slice C.window a z).Pairwise (· ≤ ·)) :
    StrictMono (fun r => N*C.blockDegree a (wordSlice C.word a z r)+(wordSlice C.word a z r).val) := by
  intro r s hrs
  have hh := (List.pairwise_ofFn.mp hs) hrs
  have he : C.window ⟨a.val+r.val,by have := r.isLt; have := z.isLt; omega⟩ ≠
      C.window ⟨a.val+s.val,by have := s.isLt; have := z.isLt; omega⟩ := by
    intro h
    have hv := congrArg Fin.val (C.window_injective h)
    change a.val+r.val = a.val+s.val at hv
    exact (ne_of_lt hrs) (Fin.ext (by omega))
  have hl := lt_of_le_of_ne hh he
  dsimp only
  unfold window at hl
  rw [C.block_weight,C.block_weight]
  exact_mod_cast hl
end ResidueChamber
end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
open AffineWindow
variable {K : Type} [Field K] {N L : ℕ}
variable (C D : ResidueChamber (K := K) (N := N))
theorem fixed_stage_minimum_iff_window (hN : 0 < N) (ht : C.top = D.top)
    (c : Fin (L+1) → Fin (N+1)) (hc : Monotone c)
    (h0 : c 0 = 0) (hl : c (Fin.last L) = Fin.last N)
    (hstage : ∀ r, C.stage (c r) = D.stage (c r))
    (hsorted : ∀ r : Fin L, (slice C.window (c r.castSucc) (c r.succ)).Pairwise (· ≤ ·)) :
    D.length = C.length ↔ D.window = C.window := by
  constructor
  · intro he
    have hlen := C.fixed_stage_length D hN ht c hc h0 hl hstage hsorted
    have hz : ((blocks D.window c).map (pairs disorder)).sum = 0 := by omega
    have hb : blocks C.window c = blocks D.window c := by
      apply sorted_blocks_eq_of_zero _ _ _ hz
      apply blocks_forall₂
      intro r
      exact ⟨C.window_slice_perm D ht _ _ (hstage _) (hstage _),hsorted r⟩
    have hh := congrArg List.flatten hb
    rw [flatten_blocks _ _ hc,flatten_blocks _ _ hc,h0,hl,slice_full,slice_full] at hh
    exact (List.ofFn_inj.mp hh).symm
  · intro he
    simp only [length,he]
lemma word_eq_of_window_eq (hN : 0 < N) (hw : D.window = C.window) : D.word = C.word := by
  apply Equiv.ext
  intro i
  have hh := congrArg (fun f : Fin N → ℤ => f i % (N : ℤ)) hw
  rw [D.window_mod hN,C.window_mod hN] at hh
  exact Fin.ext (by exact_mod_cast hh)
lemma stage_degree_eq_of_word_eq (ht : C.top = D.top) (hw : D.word = C.word)
    (r : Fin (N+1)) (i : Fin N) :
    pivotDegree (D.stage r) (D.hasStage r) i = pivotDegree (C.stage r) (C.hasStage r) i := by
  simp only [C.stage_degree,D.stage_degree,ht,hw]

def blockIndex (a z : Fin (N+1)) (r : Fin (z.val-a.val+1)) : Fin (N+1) :=
  ⟨a.val+r.val,by have := r.isLt; have := z.isLt; omega⟩
lemma blockIndex_zero (a z : Fin (N+1)) : blockIndex a z 0 = a := Fin.ext (by simp [blockIndex])
lemma blockIndex_last (a z : Fin (N+1)) (haz : a ≤ z) :
    blockIndex a z (Fin.last (z.val-a.val)) = z := Fin.ext (by simp only [blockIndex,Fin.val_mk,Fin.val_last]; omega)
lemma blockIndex_left (a z : Fin (N+1)) (r : Fin (z.val-a.val+1)) : a ≤ blockIndex a z r := by
  change a.val ≤ a.val+r.val
  omega
lemma blockIndex_right (a z : Fin (N+1)) (haz : a ≤ z) (r : Fin (z.val-a.val+1)) : blockIndex a z r ≤ z := by
  change a.val+r.val ≤ z.val
  have := r.isLt
  omega
noncomputable def blockFlag (b : Fin N → V K N)
    (hb : ∀ r, C.stage r = diagonalModule b (wordPrefix C.word r))
    (a z : Fin (N+1)) (haz : a ≤ z)
    (ha : C.stage a = D.stage a) (hz : C.stage z = D.stage z)
    (r : Fin (z.val-a.val+1)) : SelectedInterval (C.blockBasis b a) (wordSlice C.word a z) :=
  ⟨D.stage (blockIndex a z r),by
    rw [C.block_lower b hb a z haz,hz]
    exact D.strict.antitone (blockIndex_right a z haz r),by
    rw [C.block_upper b hb a,ha]
    exact D.strict.antitone (blockIndex_left a z r)⟩
lemma blockFlag_strict (b : Fin N → V K N)
    (hb : ∀ r, C.stage r = diagonalModule b (wordPrefix C.word r))
    (a z : Fin (N+1)) (haz : a ≤ z)
    (ha : C.stage a = D.stage a) (hz : C.stage z = D.stage z) :
    StrictAnti (C.blockFlag D b hb a z haz ha hz) := by
  intro r s hrs
  change D.stage (blockIndex a z s) < D.stage (blockIndex a z r)
  apply D.strict
  change a.val+r.val < a.val+s.val
  omega
lemma blockFlag_prefix_of_word (ht : C.top = D.top) (hw : D.word = C.word)
    (b : Fin N → V K N) (hb : ∀ i, Leading (b i) i (pivotDegree C.top C.hasTop i))
    (hstage : ∀ r, C.stage r = diagonalModule b (wordPrefix C.word r))
    (a z : Fin (N+1)) (haz : a ≤ z)
    (ha : C.stage a = D.stage a) (hz : C.stage z = D.stage z)
    (r : Fin (z.val-a.val+1)) (hr0 : 0 < r.val) (hrz : r.val < z.val-a.val) :
    PrefixPattern (C.blockBasis b a) (C.blockDegree a) (C.blockBasis_leading b hb a)
      (wordSlice C.word a z) (C.blockFlag D b hstage a z haz ha hz r) := by
  refine ⟨r.val,hr0,hrz,?_⟩
  intro s
  change pivotDegree (D.stage (blockIndex a z r)) _ (wordSlice C.word a z s) = _ ↔ _
  rw [C.stage_degree_eq_of_word_eq D ht hw]
  rw [C.stage_degree]
  simp only [wordSlice,blockIndex,blockDegree,Equiv.symm_apply_apply,Fin.val_mk]
  rw [ite_eq_right (show ¬ a.val+s.val < a.val from by omega)]
  split_ifs <;> omega
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N M : ℕ}
variable (C : ResidueChamber (K := K) (N := N))

theorem prescribed_refinement
    (B : Fin (M+1) → Submodule K[X] (V K N))
    (hB : ∀ r, HasPivots (B r)) (hanti : Antitone B)
    (hzero : B 0 = C.top) (hbelow : ∀ r, powerShift C.top 1 ≤ B r)
    (k : Fin (M+1) → Fin (N+1))
    (hdegree : ∀ r i, pivotDegree (B r) (hB r) i =
      pivotDegree C.top C.hasTop i + if (C.word.symm i).val < (k r).val then 1 else 0) :
    ∃ D : ResidueChamber (K := K) (N := N), D.top = C.top ∧ D.window = C.window ∧
      ∀ r, D.stage (k r) = B r := by
  classical
  obtain ⟨b,hmem,hlead,hmonic,hspan⟩ := simultaneous_minimal_basis C.top C.hasTop B hB hanti hzero hbelow
  have htop : Submodule.span K[X] (Set.range b) = C.top := by
    simpa only [hzero,ite_true] using hspan 0
  let D := diagonalChamber b (pivotDegree C.top C.hasTop) hlead C.word
  refine ⟨D,htop,?_,?_⟩
  · funext r
    exact diagonalChamber_window b (pivotDegree C.top C.hasTop) hlead C.word r
  · intro r
    change diagonalModule b (wordPrefix C.word (k r)) = B r
    rw [← hspan r]
    unfold diagonalModule
    congr 2
    funext i
    rw [hdegree r i]
    simp only [diagonalFamily,wordPrefix,Finset.mem_filter,Finset.mem_univ,true_and]
    split_ifs <;> simp_all
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

theorem finite_simultaneous_basis (A : Submodule K[X] (V K N)) (hA : HasPivots A)
    (s : Finset (Submodule K[X] (V K N))) (hAs : A ∈ s)
    (hs : (s : Set (Submodule K[X] (V K N))).Pairwise (fun D E => D ≤ E ∨ E ≤ D))
    (hinterval : ∀ D ∈ s, powerShift A 1 ≤ D ∧ D ≤ A) :
    ∃ b : Fin N → V K N,
      (∀ i, Leading (b i) i (pivotDegree A hA i)) ∧
      Submodule.span K[X] (Set.range b) = A ∧
      ∀ D ∈ s, ∀ hP : HasPivots D,
        Submodule.span K[X] (Set.range fun i =>
          if pivotDegree D hP i = pivotDegree A hA i then b i else (Polynomial.X : K[X]) • b i) = D := by
  classical
  have hP (D : Submodule K[X] (V K N)) (hD : D ∈ s) : HasPivots D := by
    intro i
    obtain ⟨m,v,hv,hl⟩ := powerShift_hasPivots A hA 1 i
    exact ⟨m,v,(hinterval D hD).1 hv,hl⟩
  let S (i : Fin N) : Finset (Submodule K[X] (V K N)) :=
    s.filter fun D => ∃ hD : HasPivots D, pivotDegree D hD i = pivotDegree A hA i
  have hS (i : Fin N) : (S i).Nonempty := by
    refine ⟨A,Finset.mem_filter.mpr ⟨hAs,hA,rfl⟩⟩
  have hmin (i : Fin N) : ∃ D, Minimal (fun D => D ∈ S i) D :=
    ((S i).finite_toSet.isPWO.exists_minimal (hS i))
  choose B hB using hmin
  have hBs (i : Fin N) : B i ∈ s := (Finset.mem_filter.mp (hB i).1).1
  have hdeg (i : Fin N) : pivotDegree (B i) (hP (B i) (hBs i)) i = pivotDegree A hA i :=
    (Finset.mem_filter.mp (hB i).1).2.choose_spec
  let b (i : Fin N) := pivot (B i) (hP (B i) (hBs i)) i
  have hb (i : Fin N) : Leading (b i) i (pivotDegree A hA i) := by
    rw [← hdeg i]
    exact pivot_leading _ _ _
  have hmem (i : Fin N) : b i ∈ A := (hinterval _ (hBs i)).2 (pivot_mem _ _ _)
  have hspan (D : Submodule K[X] (V K N)) (hD : D ∈ s) (hPD : HasPivots D) :
      Submodule.span K[X] (Set.range fun i =>
        if pivotDegree D hPD i = pivotDegree A hA i then b i else (Polynomial.X : K[X]) • b i) = D := by
    let c (i : Fin N) := if pivotDegree D hPD i = pivotDegree A hA i then b i else (Polynomial.X : K[X]) • b i
    have hinc (i : Fin N) := interval_pivot_increment hA hPD (hinterval D hD).2 (hinterval D hD).1 i
    have hc (i : Fin N) : c i ∈ D := by
      dsimp only [c]
      split_ifs with he
      · have hDi : D ∈ S i := Finset.mem_filter.mpr ⟨hD,hPD,he⟩
        have hBD : B i ≤ D := by
          by_cases heq : B i = D
          · exact heq.le
          · rcases hs (hBs i) hD heq with h | h
            · exact h
            · exact (hB i).2 hDi h
        exact hBD (pivot_mem _ _ _)
      · apply (hinterval D hD).1
        refine ⟨b i,hmem i,?_⟩
        simp [powerLinear]
    have hcl (i : Fin N) : Leading (c i) i (pivotDegree D hPD i) := by
      dsimp only [c]
      split_ifs with he
      · rw [he]; exact hb i
      · have hh : pivotDegree D hPD i = pivotDegree A hA i+1 := (hinc i).resolve_left he
        rw [hh]
        simpa using leading_X_pow (hb i) 1
    exact span_of_minimal D c (pivotDegree D hPD) hc hcl (fun hv hl => pivotDegree_min _ _ _ hv hl)
  refine ⟨b,hb,?_,hspan⟩
  simpa only [ite_true] using hspan A hAs hA

namespace ResidueChamber
variable (C : ResidueChamber (K := K) (N := N))

theorem face_prescribed_refinement
    (s : Finset (Submodule K[X] (V K N))) (htop : C.top ∈ s)
    (hs : (s : Set (Submodule K[X] (V K N))).Pairwise (fun D E => D ≤ E ∨ E ≤ D))
    (hi : ∀ D ∈ s, powerShift C.top 1 ≤ D ∧ D ≤ C.top)
    (hp : ∀ D ∈ s, ∃ (r : Fin (N+1)) (hP : HasPivots D),
      ∀ i, pivotDegree D hP i = pivotDegree C.top C.hasTop i +
        if (C.word.symm i).val < r.val then 1 else 0) :
    ∃ E : ResidueChamber (K := K) (N := N), E.top = C.top ∧ E.window = C.window ∧
      ∀ D ∈ s, ∃ r, E.stage r = D := by
  classical
  obtain ⟨b,hb,hspan,hDs⟩ := finite_simultaneous_basis C.top C.hasTop s htop hs hi
  let E := diagonalChamber b (pivotDegree C.top C.hasTop) hb C.word
  refine ⟨E,hspan,?_,?_⟩
  · funext r
    exact diagonalChamber_window b (pivotDegree C.top C.hasTop) hb C.word r
  · intro D hD
    obtain ⟨r,hP,hdegree⟩ := hp D hD
    refine ⟨r,?_⟩
    change diagonalModule b (wordPrefix C.word r) = D
    rw [← hDs D hD hP]
    unfold diagonalModule
    congr 2
    funext i
    rw [hdegree i]
    simp only [diagonalFamily,wordPrefix,Finset.mem_filter,Finset.mem_univ,true_and]
    split_ifs <;> simp_all
end ResidueChamber
end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}
variable (C : ResidueChamber (K := K) (N := N))
def HasProfile (D : Submodule K[X] (V K N)) (r : Fin (N+1)) : Prop :=
  ∃ hD : HasPivots D, ∀ i, pivotDegree D hD i = pivotDegree C.top C.hasTop i +
    if (C.word.symm i).val < r.val then 1 else 0
lemma stage_hasProfile (r : Fin (N+1)) : C.HasProfile (C.stage r) r := ⟨C.hasStage r,C.stage_degree r⟩
lemma top_hasProfile : C.HasProfile C.top 0 := by
  simpa only [C.initial] using C.stage_hasProfile 0
lemma profile_increments {D : Submodule K[X] (V K N)} {r : Fin (N+1)} (h : C.HasProfile D r) :
    ∃ hD : HasPivots D, incrementSet C.top D C.hasTop hD =
      incrementSet C.top (C.stage r) C.hasTop (C.hasStage r) := by
  obtain ⟨hD,hdeg⟩ := h
  refine ⟨hD,?_⟩
  ext i
  simp only [incrementSet,Finset.mem_filter,Finset.mem_univ,true_and,hdeg,C.stage_degree]
lemma profile_unique {D : Submodule K[X] (V K N)} {r s : Fin (N+1)}
    (hr : C.HasProfile D r) (hs : C.HasProfile D s) : r = s := by
  obtain ⟨hD,hri⟩ := C.profile_increments hr
  obtain ⟨_,hsi⟩ := C.profile_increments hs
  have h := congrArg Finset.card (hri.symm.trans hsi)
  rw [C.increments_card,C.increments_card] at h
  exact Fin.ext h
lemma profile_rank_antitone {D E : Submodule K[X] (V K N)} {r s : Fin (N+1)}
    (hD : C.HasProfile D r) (hE : C.HasProfile E s) (hDE : D ≤ E) : s ≤ r := by
  obtain ⟨hDP,hd⟩ := hD
  obtain ⟨hEP,he⟩ := hE
  by_contra hh
  have hrs : r.val < s.val := lt_of_not_ge hh
  let i : Fin N := ⟨r.val,by have := s.isLt; omega⟩
  have h := pivotDegree_antitone hEP hDP hDE (C.word i)
  rw [hd,he] at h
  simp only [Equiv.symm_apply_apply] at h
  change (pivotDegree C.top C.hasTop (C.word i) + if r.val < s.val then 1 else 0) ≤
    (pivotDegree C.top C.hasTop (C.word i) + if r.val < r.val then 1 else 0) at h
  simp only [hrs,ite_true,lt_self_iff_false,ite_false,Nat.add_zero] at h
  omega
lemma profile_compare {D E : Submodule K[X] (V K N)} {r s : Fin (N+1)}
    (hD : C.HasProfile D r) (hE : C.HasProfile E s)
    (hDE : D ≤ E ∨ E ≤ D) (hrs : r ≤ s) : E ≤ D := by
  rcases hDE with h | h
  · have he : r = s := le_antisymm hrs (C.profile_rank_antitone hD hE h)
    obtain ⟨hDP,hd⟩ := hD
    obtain ⟨hEP,he'⟩ := hE
    have hEq : E = D := eq_of_le_same_pivots hEP hDP h (fun i => by rw [hd,he',he])
    exact hEq.le
  · exact h

lemma prefixPattern_iff_profile (b : Fin N → V K N)
    (hb : ∀ i, Leading (b i) i (pivotDegree C.top C.hasTop i))
    (a z : Fin (N+1)) (haz : a ≤ z)
    (D : SelectedInterval (C.blockBasis b a) (wordSlice C.word a z)) :
    PrefixPattern (C.blockBasis b a) (C.blockDegree a) (C.blockBasis_leading b hb a)
      (wordSlice C.word a z) D ↔
      ∃ r : Fin (N+1), a < r ∧ r < z ∧ C.HasProfile D.val r := by
  let hDP := selectedInterval_hasPivots (C.blockBasis b a) (C.blockDegree a)
    (C.blockBasis_leading b hb a) (wordSlice C.word a z) D
  constructor
  · rintro ⟨k,hk0,hkz,hpat⟩
    let r : Fin (N+1) := ⟨a.val+k,by have := z.isLt; omega⟩
    refine ⟨r,(by change a.val < a.val+k; omega),(by change a.val+k < z.val; omega),hDP,?_⟩
    intro i
    have hp := selected_pivot_bounds (C.blockBasis b a) (C.blockDegree a)
      (C.blockBasis_leading b hb a) (wordSlice C.word a z) D i
    by_cases hi : i ∈ Finset.univ.image (wordSlice C.word a z)
    · obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp hi
      have he := hpat s
      have hb0 : C.blockDegree a (wordSlice C.word a z s) =
          pivotDegree C.top C.hasTop (wordSlice C.word a z s) := by
        simp only [blockDegree,wordSlice,Equiv.symm_apply_apply,Fin.val_mk]
        rw [ite_eq_right (by omega),Nat.add_zero]
      rw [hb0] at hp he
      have hm : wordSlice C.word a z s ∈ Finset.univ.image (wordSlice C.word a z) :=
        Finset.mem_image.mpr ⟨s,Finset.mem_univ _,rfl⟩
      simp only [hm,ite_true] at hp
      dsimp only [wordSlice] at hp he
      simp only [wordSlice,Equiv.symm_apply_apply,Fin.val_mk]
      change pivotDegree D.val hDP _ = pivotDegree C.top C.hasTop _ +
        if a.val+s.val < a.val+k then 1 else 0
      split_ifs <;> omega
    · have hn := (mem_wordSlice_image C.word a z i).not.mp hi
      simp only [hi,ite_false,Nat.add_zero] at hp
      have he := le_antisymm hp.2 hp.1
      rw [he]
      dsimp only [blockDegree,r]
      split_ifs <;> omega
  · rintro ⟨r,har,hrz,hprof⟩
    obtain ⟨hD,hdeg⟩ := hprof
    refine ⟨r.val-a.val,(by change a.val < r.val at har; omega),?_,?_⟩
    · change r.val < z.val at hrz
      change a.val < r.val at har
      omega
    · intro s
      rw [hdeg]
      simp only [wordSlice,blockDegree,Equiv.symm_apply_apply,Fin.val_mk]
      simp only [ite_eq_right (show ¬ a.val+s.val < a.val from by omega),Nat.add_zero]
      change a.val < r.val at har
      split_ifs <;> omega
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
open InfiniteChains AffineWindow
variable {K : Type} [Field K] {N L : ℕ}
variable (C : ResidueChamber (K := K) (N := N))
lemma profile_stage_le_top (r : Fin (N+1)) : C.stage r ≤ C.top := by
  rw [← C.initial]
  exact C.strict.antitone (Fin.zero_le _)
lemma stage_hasProfile_of_window (E : ResidueChamber (K := K) (N := N)) (hN : 0 < N)
    (ht : E.top = C.top) (hw : E.window = C.window) (r : Fin (N+1)) :
    C.HasProfile (E.stage r) r := by
  refine ⟨E.hasStage r,?_⟩
  intro i
  have he := C.word_eq_of_window_eq E hN hw
  simpa only [ht,he] using E.stage_degree r i
lemma cuts_interval (c : Fin (L+1) → Fin (N+1)) (_ : StrictMono c)
    (h0 : c 0 = 0) (hl : c (Fin.last L) = Fin.last N)
    (r : Fin (N+1)) (hr : r ∉ Finset.univ.image c) :
    ∃ j : Fin L, c j.castSucc < r ∧ r < c j.succ := by
  classical
  let S : Finset (Fin (L+1)) := Finset.univ.filter (fun j => c j ≤ r)
  have hS : S.Nonempty := ⟨0,by simp [S,h0]⟩
  let j := S.max' hS
  have hj : c j ≤ r := (Finset.mem_filter.mp (Finset.max'_mem S hS)).2
  have hneq (k : Fin (L+1)) : r ≠ c k := by
    intro he
    exact hr (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,he.symm⟩)
  have hjL : j.val < L := by
    by_contra hh
    have he : j = Fin.last L := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
    rw [he,hl] at hj
    exact hneq (Fin.last L) ((le_antisymm (Fin.le_last r) hj).trans hl.symm)
  let k : Fin L := ⟨j.val,hjL⟩
  have hk : k.castSucc = j := Fin.ext rfl
  refine ⟨k,?_,?_⟩
  · rw [hk]; exact lt_of_le_of_ne hj (hneq j).symm
  · by_contra hh
    have hmem : k.succ ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_of_not_gt hh⟩
    have hle := Finset.le_max' S k.succ hmem
    change k.val+1 ≤ j.val at hle
    dsimp only [k] at hle
    omega

noncomputable def fixedStages (c : Fin (L+1) → Fin (N+1)) : Finset (Submodule K[X] (V K N)) :=
  Finset.univ.image (fun j => C.stage (c j))

def IntervalProfile (c : Fin (L+1) → Fin (N+1)) (D : Submodule K[X] (V K N)) : Prop :=
  ∃ j : Fin L, C.stage (c j.succ) ≤ D ∧ D ≤ C.stage (c j.castSucc) ∧
    ∃ r : Fin (N+1), c j.castSucc < r ∧ r < c j.succ ∧ C.HasProfile D r
lemma intervalProfile_interval (c : Fin (L+1) → Fin (N+1)) {D : Submodule K[X] (V K N)}
    (hD : C.IntervalProfile c D) : powerShift C.top 1 ≤ D ∧ D ≤ C.top := by
  obtain ⟨j,hlo,hup,r,_,_,_⟩ := hD
  exact ⟨(C.lower _).trans hlo,hup.trans (C.profile_stage_le_top _)⟩
lemma intervalProfile_compare_fixed (c : Fin (L+1) → Fin (N+1)) (hc : Monotone c)
    {D : Submodule K[X] (V K N)} (hD : C.IntervalProfile c D) (k : Fin (L+1)) :
    D ≤ C.stage (c k) ∨ C.stage (c k) ≤ D := by
  obtain ⟨j,hlo,hup,r,_,_,_⟩ := hD
  by_cases hk : k ≤ j.castSucc
  · exact Or.inl (hup.trans (C.strict.antitone (hc hk)))
  · exact Or.inr ((C.strict.antitone (hc (show j.succ ≤ k from by
      change j.val+1 ≤ k.val
      change ¬k.val ≤ j.val at hk
      omega))).trans hlo)
lemma intervalProfile_not_fixed (c : Fin (L+1) → Fin (N+1)) (hc : StrictMono c)
    {D : Submodule K[X] (V K N)} (hD : C.IntervalProfile c D) : D ∉ C.fixedStages c := by
  classical
  obtain ⟨j,_,_,r,har,hrz,hp⟩ := hD
  rintro hm
  obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hm
  have he : r = c k := C.profile_unique hp (hk ▸ C.stage_hasProfile (c k))
  rw [he] at har hrz
  have h1 := hc.lt_iff_lt.mp har
  have h2 := hc.lt_iff_lt.mp hrz
  change j.val < k.val at h1
  change k.val < j.val+1 at h2
  omega

def rootedMinimumLink (c : Fin (L+1) → Fin (N+1)) : InfiniteChains.Complex (Submodule K[X] (V K N)) where
  faces := {s | Disjoint s (C.fixedStages c) ∧ ∃ E : ResidueChamber (K := K) (N := N),
    E.top = C.top ∧ E.length = C.length ∧ (∀ j, E.stage (c j) = C.stage (c j)) ∧
    ∀ D ∈ s, ∃ r, E.stage r = D}
  empty_mem := by exact ⟨Finset.disjoint_empty_left _,C,rfl,rfl,(fun _ => rfl),by simp⟩
  downward := by
    intro s t hs hts
    obtain ⟨hd,E,ht,hl,hfix,hface⟩ := hs
    exact ⟨hd.mono_left hts,E,ht,hl,hfix,fun D hD => hface D (hts hD)⟩

theorem rootedMinimumLink_iff (hN : 0 < N)
    (c : Fin (L+1) → Fin (N+1)) (hc : StrictMono c)
    (h0 : c 0 = 0) (hl : c (Fin.last L) = Fin.last N)
    (hsorted : ∀ j : Fin L, (slice C.window (c j.castSucc) (c j.succ)).Pairwise (· ≤ ·))
    (s : Finset (Submodule K[X] (V K N))) :
    s ∈ (C.rootedMinimumLink c).faces ↔
      (∀ D ∈ s, C.IntervalProfile c D) ∧
      (s : Set (Submodule K[X] (V K N))).Pairwise (fun D E => D ≤ E ∨ E ≤ D) := by
  classical
  constructor
  · rintro ⟨hd,E,ht,hEl,hfix,hface⟩
    have hw := (C.fixed_stage_minimum_iff_window E hN ht.symm c hc.monotone h0 hl
      (fun j => (hfix j).symm) hsorted).mp hEl
    constructor
    · intro D hD
      obtain ⟨r,rfl⟩ := hface D hD
      have hn : r ∉ Finset.univ.image c := by
        rintro hh
        obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hh
        exact Finset.disjoint_left.mp hd hD (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,(hfix k).symm⟩)
      obtain ⟨j,hjr,hrj⟩ := cuts_interval c hc h0 hl r hn
      refine ⟨j,?_,?_,r,hjr,hrj,C.stage_hasProfile_of_window E hN ht hw r⟩
      · rw [← hfix]; exact E.strict.antitone hrj.le
      · rw [← hfix]; exact E.strict.antitone hjr.le
    · intro D hD F hF hne
      obtain ⟨r,rfl⟩ := hface D hD
      obtain ⟨t,rfl⟩ := hface F hF
      rcases le_total r t with h | h
      · exact Or.inr (E.strict.antitone h)
      · exact Or.inl (E.strict.antitone h)
  · rintro ⟨hprof,hchain⟩
    let u := s ∪ C.fixedStages c
    have htop : C.top ∈ u := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,by rw [h0,C.initial]⟩
    have hu : (u : Set (Submodule K[X] (V K N))).Pairwise (fun D E => D ≤ E ∨ E ≤ D) := by
      intro D hD E hE hne
      rcases Finset.mem_union.mp hD with hD | hD <;> rcases Finset.mem_union.mp hE with hE | hE
      · exact hchain hD hE hne
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hE
        exact C.intervalProfile_compare_fixed c hc.monotone (hprof D hD) j
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hD
        exact (C.intervalProfile_compare_fixed c hc.monotone (hprof E hE) j).symm
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hD
        obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hE
        rcases le_total (c j) (c k) with h | h
        · exact Or.inr (C.strict.antitone h)
        · exact Or.inl (C.strict.antitone h)
    have hi : ∀ D ∈ u, powerShift C.top 1 ≤ D ∧ D ≤ C.top := by
      intro D hD
      rcases Finset.mem_union.mp hD with hD | hD
      · exact C.intervalProfile_interval c (hprof D hD)
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hD
        exact ⟨C.lower _,C.profile_stage_le_top _⟩
    have hp : ∀ D ∈ u, ∃ r, C.HasProfile D r := by
      intro D hD
      rcases Finset.mem_union.mp hD with hD | hD
      · obtain ⟨j,_,_,r,_,_,hp⟩ := hprof D hD
        exact ⟨r,hp⟩
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hD
        exact ⟨c j,C.stage_hasProfile _⟩
    obtain ⟨E,ht,hw,hE⟩ := C.face_prescribed_refinement u htop hu hi hp
    refine ⟨Finset.disjoint_left.mpr (fun D hD => C.intervalProfile_not_fixed c hc (hprof D hD)),
      E,ht,?_,?_,fun D hD => hE D (Finset.mem_union_left _ hD)⟩
    · simp only [length,hw]
    · intro j
      obtain ⟨r,hr⟩ := hE (C.stage (c j)) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
      have he : r = c j := C.profile_unique
        (hr ▸ C.stage_hasProfile_of_window E hN ht hw r) (C.stage_hasProfile (c j))
      exact he ▸ hr
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
open Module InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
variable {K : Type} [Field K] {N M : ℕ}

theorem uniform_polynomial_residue_cones (n : ℕ) :
    ∃ Q R : ℕ, ∀ (K : Type) [Field K] [Fintype K] (N M : ℕ)
      (b : Fin N → V K N) (a : Fin N → ℕ) (hb : ∀ i, Leading (b i) i (a i))
      (σ : Fin M → Fin N), StrictMono (fun i => N*a (σ i)+(σ i).val) →
      n+2 ≤ M → Q < Fintype.card K →
        Nonempty (BoundedCone (prefixPatternComplex b a hb σ) n R) := by
  classical
  obtain ⟨Q,R,h⟩ := SphericalOpposition.CompleteFlag.exists_uniform_cones n
  refine ⟨Q,R,?_⟩
  intro K _ _ N M b a hb σ hσ hM hq
  let e := selectedIntervalEquiv b a hb σ hσ
  let X := prefixPatternComplex b a hb σ
  let Y := (FinitePivots.prefixFlag K M).complex
  have he : ∀ s, s ∈ X.faces ↔ s.image e ∈ Y.faces := prefixPattern_faces_equiv b a hb σ hσ
  have hg (s) (hs : s ∈ Y.faces) : s.image e.symm ∈ X.faces := by
    apply (he _).mpr
    simpa only [Finset.image_image,Function.comp_def,OrderIso.apply_symm_apply,Finset.image_id'] using hs
  exact ⟨(h K (Fin M → K) M (FinitePivots.prefixFlag K M) hM hq).some.retract e e.symm
    (fun s hs => (he s).mp hs) hg (fun _ _ => e.injective.injOn)
    (fun _ _ => e.symm.injective.injOn) (fun _ _ _ _ => e.symm_apply_apply _)⟩
end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
open InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
variable {K : Type} [Field K] {N : ℕ}
variable (C : ResidueChamber (K := K) (N := N))
def ProfileBetween (a z : Fin (N+1)) (D : Submodule K[X] (V K N)) : Prop :=
  C.stage z ≤ D ∧ D ≤ C.stage a ∧ ∃ r : Fin (N+1), a < r ∧ r < z ∧ C.HasProfile D r
def profileIntervalComplex (a z : Fin (N+1)) : InfiniteChains.Complex (Submodule K[X] (V K N)) where
  faces := {s | (∀ D ∈ s, C.ProfileBetween a z D) ∧
    (s : Set (Submodule K[X] (V K N))).Pairwise (fun D E => D ≤ E ∨ E ≤ D)}
  empty_mem := by simp
  downward := by intro s t hs hts; exact ⟨fun D hD => hs.1 D (hts hD),hs.2.mono hts⟩
lemma profileInterval_empty (a z : Fin (N+1)) (h : z.val ≤ a.val+1)
    (s : Finset (Submodule K[X] (V K N))) (hs : s ∈ (C.profileIntervalComplex a z).faces) : s = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro D hD
  obtain ⟨_,_,r,har,hrz,_⟩ := hs.1 D hD
  change a.val < r.val at har
  change r.val < z.val at hrz
  omega
lemma profileInterval_faces_selected (b : Fin N → V K N)
    (hb : ∀ i, Leading (b i) i (pivotDegree C.top C.hasTop i))
    (hstage : ∀ r, C.stage r = diagonalModule b (wordPrefix C.word r))
    (a z : Fin (N+1)) (haz : a ≤ z)
    (s : Finset (SelectedInterval (C.blockBasis b a) (wordSlice C.word a z))) :
    s ∈ (prefixPatternComplex (C.blockBasis b a) (C.blockDegree a) (C.blockBasis_leading b hb a)
      (wordSlice C.word a z)).faces ↔ s.image Subtype.val ∈ (C.profileIntervalComplex a z).faces := by
  classical
  constructor
  · rintro ⟨hpat,hpair⟩
    constructor
    · intro D hD
      obtain ⟨E,hE,rfl⟩ := Finset.mem_image.mp hD
      refine ⟨?_,?_,(C.prefixPattern_iff_profile b hb a z haz E).mp (hpat E hE)⟩
      · simpa only [C.block_lower b hstage a z haz] using E.property.1
      · simpa only [C.block_upper b hstage a] using E.property.2
    · intro D hD E hE hne
      obtain ⟨D,hDs,rfl⟩ := Finset.mem_image.mp hD
      obtain ⟨E,hEs,rfl⟩ := Finset.mem_image.mp hE
      exact hpair hDs hEs (fun hh => hne (congrArg Subtype.val hh))
  · rintro ⟨hprof,hpair⟩
    constructor
    · intro D hD
      exact (C.prefixPattern_iff_profile b hb a z haz D).mpr
        (hprof D.val (Finset.mem_image.mpr ⟨D,hD,rfl⟩)).2.2
    · intro D hD E hE hne
      exact hpair (Finset.mem_image.mpr ⟨D,hD,rfl⟩) (Finset.mem_image.mpr ⟨E,hE,rfl⟩)
        (fun hh => hne (Subtype.ext hh))
noncomputable def profileIntervalCone (b : Fin N → V K N)
    (hb : ∀ i, Leading (b i) i (pivotDegree C.top C.hasTop i))
    (hstage : ∀ r, C.stage r = diagonalModule b (wordPrefix C.word r))
    (a z : Fin (N+1)) (haz : a ≤ z) {n R : ℕ}
    (H : BoundedCone (prefixPatternComplex (C.blockBasis b a) (C.blockDegree a)
      (C.blockBasis_leading b hb a) (wordSlice C.word a z)) n R) :
    BoundedCone (C.profileIntervalComplex a z) n R := by
  classical
  let A := SelectedInterval (C.blockBasis b a) (wordSlice C.word a z)
  let d0 : A := ⟨C.stage a,by rw [C.block_lower b hstage a z haz]; exact C.strict.antitone haz,
    by rw [C.block_upper b hstage a]⟩
  let f : Submodule K[X] (V K N) → A := fun D =>
    if h : C.stage z ≤ D ∧ D ≤ C.stage a then
      ⟨D,by rw [C.block_lower b hstage a z haz]; exact h.1,
        by rw [C.block_upper b hstage a]; exact h.2⟩ else d0
  have hfval (D : Submodule K[X] (V K N)) (hD : C.stage z ≤ D ∧ D ≤ C.stage a) : (f D).val = D := by
    simp only [f,dite_eq_left hD]
  have hret (s) (hs : s ∈ (C.profileIntervalComplex a z).faces) (D) (hD : D ∈ s) : (f D).val = D :=
    hfval D ⟨(hs.1 D hD).1,(hs.1 D hD).2.1⟩
  have him (s) (hs : s ∈ (C.profileIntervalComplex a z).faces) : (s.image f).image Subtype.val = s := by
    rw [Finset.image_image]
    exact (Finset.image_congr (fun D hD => hret s hs D hD)).trans (Finset.image_id)
  refine H.retract f Subtype.val ?_ ?_ ?_ (fun _ _ => Subtype.val_injective.injOn) hret
  · intro s hs
    apply (C.profileInterval_faces_selected b hb hstage a z haz (s.image f)).mpr
    rwa [him s hs]
  · intro s hs
    exact (C.profileInterval_faces_selected b hb hstage a z haz s).mp hs
  · intro s hs D hD E hE hh
    have he := congrArg Subtype.val hh
    rwa [hret s hs D hD,hret s hs E hE] at he

theorem uniform_profileInterval_cones (n : ℕ) :
    ∃ Q R : ℕ, ∀ (K : Type) [Field K] [Fintype K] (N : ℕ)
      (C : ResidueChamber (K := K) (N := N)) (a z : Fin (N+1)),
      n+2 ≤ z.val-a.val → (AffineWindow.slice C.window a z).Pairwise (· ≤ ·) →
      Q < Fintype.card K → Nonempty (BoundedCone (C.profileIntervalComplex a z) n R) := by
  classical
  obtain ⟨Q,R,h⟩ := uniform_polynomial_residue_cones n
  refine ⟨Q,R,?_⟩
  intro K _ _ N C a z hdim hsorted hq
  obtain ⟨b,hb,_,_,hstage⟩ := C.diagonal_representation
  have haz : a ≤ z := by change a.val ≤ z.val; omega
  exact ⟨C.profileIntervalCone b hb hstage a z haz
    (h K N (z.val-a.val) (C.blockBasis b a) (C.blockDegree a)
      (C.blockBasis_leading b hb a) (wordSlice C.word a z)
      (C.sorted_block_selection a z hsorted) hdim hq).some⟩
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
open InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
variable {K : Type} [Field K] {N L : ℕ}
variable (C : ResidueChamber (K := K) (N := N))
lemma profileBetween_unique (c : Fin (L+1) → Fin (N+1)) (hc : StrictMono c)
    {i j : Fin L} {D : Submodule K[X] (V K N)}
    (hi : C.ProfileBetween (c i.castSucc) (c i.succ) D)
    (hj : C.ProfileBetween (c j.castSucc) (c j.succ) D) : i = j := by
  obtain ⟨_,_,r,hir,hri,hr⟩ := hi
  obtain ⟨_,_,t,hjt,htj,ht⟩ := hj
  have he : r = t := C.profile_unique hr ht
  subst t
  have h1 : j.castSucc < i.succ := hc.lt_iff_lt.mp (hjt.trans hri)
  have h2 : i.castSucc < j.succ := hc.lt_iff_lt.mp (hir.trans htj)
  apply Fin.ext
  change j.val < i.val+1 at h1
  change i.val < j.val+1 at h2
  omega
lemma profileBetween_compare (c : Fin (L+1) → Fin (N+1)) (hc : Monotone c)
    {i j : Fin L} {D E : Submodule K[X] (V K N)} (hij : i < j)
    (hi : C.ProfileBetween (c i.castSucc) (c i.succ) D)
    (hj : C.ProfileBetween (c j.castSucc) (c j.succ) E) : E ≤ D := by
  apply hj.2.1.trans
  apply (C.strict.antitone (hc (show i.succ ≤ j.castSucc from by
    change i.val+1 ≤ j.val
    change i.val < j.val at hij
    omega))).trans hi.1

theorem rootedMinimumLink_exact_of_join (hN : 0 < N)
    (c : Fin (L+1) → Fin (N+1)) (hc : StrictMono c)
    (h0 : c 0 = 0) (hl : c (Fin.last L) = Fin.last N)
    (hsorted : ∀ j : Fin L, (AffineWindow.slice C.window (c j.castSucc) (c j.succ)).Pairwise (· ≤ ·))
    (r : ℕ) (H : ExactIn (Join.finiteComplex
      (fun j : Fin L => C.profileIntervalComplex (c j.castSucc) (c j.succ))).faces r) :
    ExactIn (C.rootedMinimumLink c).faces r := by
  classical
  have hL : 0 < L := by
    by_contra hh
    have he : Fin.last L = (0 : Fin (L+1)) := Fin.ext (by simp; omega)
    rw [he,h0] at hl
    have hh := congrArg Fin.val hl
    simp at hh
    omega
  let tag : Submodule K[X] (V K N) → Fin L := fun D =>
    if h : C.IntervalProfile c D then h.choose else ⟨0,hL⟩
  have htag (D) (hD : C.IntervalProfile c D) :
      C.ProfileBetween (c (tag D).castSucc) (c (tag D).succ) D := by
    simpa only [tag,dite_eq_left hD,ProfileBetween] using hD.choose_spec
  let f : Submodule K[X] (V K N) → Fin L × Submodule K[X] (V K N) := fun D => (tag D,D)
  let X := Join.finiteComplex (fun j : Fin L => C.profileIntervalComplex (c j.castSucc) (c j.succ))
  have hf (s) (hs : s ∈ (C.rootedMinimumLink c).faces) : s.image f ∈ X.faces := by
    have hh := (C.rootedMinimumLink_iff hN c hc h0 hl hsorted s).mp hs
    intro j
    constructor
    · intro D hD
      have hm := (Join.mem_fiber (s.image f) j D).mp hD
      obtain ⟨E,hE,he⟩ := Finset.mem_image.mp hm
      have he2 : E = D := congrArg Prod.snd he
      subst E
      have ht : tag D = j := congrArg Prod.fst he
      exact ht ▸ htag D (hh.1 D hE)
    · intro D hD E hE hne
      have hin (F) (hF : F ∈ Join.fiber (s.image f) j) : F ∈ s := by
        obtain ⟨G,hG,hg⟩ := Finset.mem_image.mp ((Join.mem_fiber (s.image f) j F).mp hF)
        have he : G = F := congrArg Prod.snd hg
        exact he ▸ hG
      exact hh.2 (hin D hD) (hin E hE) hne
  have hg (s) (hs : s ∈ X.faces) : s.image Prod.snd ∈ (C.rootedMinimumLink c).faces := by
    apply (C.rootedMinimumLink_iff hN c hc h0 hl hsorted _).mpr
    constructor
    · intro D hD
      obtain ⟨⟨i,E⟩,hE,rfl⟩ := Finset.mem_image.mp hD
      exact ⟨i,(hs i).1 E ((Join.mem_fiber s i E).mpr hE)⟩
    · intro D hD E hE hne
      obtain ⟨⟨i,D⟩,hDi,rfl⟩ := Finset.mem_image.mp hD
      obtain ⟨⟨j,E⟩,hEj,rfl⟩ := Finset.mem_image.mp hE
      have hi := (hs i).1 D ((Join.mem_fiber s i D).mpr hDi)
      have hj := (hs j).1 E ((Join.mem_fiber s j E).mpr hEj)
      rcases lt_trichotomy i j with hij | hij | hij
      · exact Or.inr (C.profileBetween_compare c hc.monotone hij hi hj)
      · subst j
        exact (hs i).2 ((Join.mem_fiber s i D).mpr hDi) ((Join.mem_fiber s i E).mpr hEj) hne
      · exact Or.inl (C.profileBetween_compare c hc.monotone hij hj hi)
  apply exactIn_retract f Prod.snd _ X.faces hf hg ?_ ?_ (by intros; rfl) r H
  · intro s hs D hD E hE hh
    exact congrArg Prod.snd hh
  · intro s hs x hx y hy hh
    rcases x with ⟨i,D⟩
    rcases y with ⟨j,E⟩
    change D = E at hh
    subst E
    have hi := (hs i).1 D ((Join.mem_fiber s i D).mpr hx)
    have hj := (hs j).1 D ((Join.mem_fiber s j D).mpr hy)
    have he := C.profileBetween_unique c hc hi hj
    exact congrArg (fun k => (k,D)) he
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
open InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
private lemma sum_gaps {L : ℕ} (c : Fin (L+1) → ℕ) (hc : Monotone c) :
    (∑ j : Fin L, (c j.succ - c j.castSucc)) + c 0 = c (Fin.last L) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Fin.sum_univ_succ]
    have ht := ih (fun i : Fin (L+1) => c i.succ) (fun i j hij => hc (Fin.succ_le_succ_iff.mpr hij))
    have hle := hc (Fin.zero_le (1 : Fin (L+2)))
    change (c 1-c 0)+(∑ j : Fin L, (c j.succ.succ - c j.castSucc.succ))+c 0 = c (Fin.last (L+1))
    change (∑ j : Fin L, (c j.succ.succ - c j.castSucc.succ))+c 1 = c (Fin.last (L+1)) at ht
    omega

theorem uniform_rootedMinimumLink_exact (N : ℕ) :
    ∃ Q : ℕ, ∀ (K : Type) [Field K] [Fintype K]
      (C : ResidueChamber (K := K) (N := N)) (L : ℕ)
      (c : Fin (L+1) → Fin (N+1)),
      0 < N → StrictMono c → c 0 = 0 → c (Fin.last L) = Fin.last N →
      (∀ j : Fin L, (AffineWindow.slice C.window (c j.castSucc) (c j.succ)).Pairwise (· ≤ ·)) →
      Q < Fintype.card K → ∀ r < N-L, ExactIn (C.rootedMinimumLink c).faces r := by
  classical
  choose Q R h using uniform_profileInterval_cones
  let T := (Finset.range (N+1)).sup Q
  refine ⟨T,?_⟩
  intro K _ _ C L c hN hc h0 hl hsort hq r hr
  let a : Fin L → ℕ := fun j => (c j.succ).val-(c j.castSucc).val-1
  have hstep (j : Fin L) : (c j.castSucc).val < (c j.succ).val := hc (by exact Fin.castSucc_lt_succ)
  have hsum : (∑ j, a j) + L = N := by
    have hg := sum_gaps (fun j => (c j).val) (fun i j hij => hc.monotone hij)
    rw [h0,hl] at hg
    simp only [Fin.val_zero,Fin.val_last,Nat.add_zero] at hg
    have he : (∑ j : Fin L, (a j+1)) = (∑ j : Fin L, ((c j.succ).val-(c j.castSucc).val)) := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [a]
      have hh := hstep j
      omega
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] using he.trans hg
  apply C.rootedMinimumLink_exact_of_join hN c hc h0 hl hsort r
  have hr' : r < ∑ j, a j := by omega
  cases L with
  | zero => simp at hr'
  | succ L =>
    apply Join.exactIn_finiteComplex_all L _ a ?_ ?_ r hr'
    · intro j hj
      have hd := (c j.succ).isLt
      have hs := hstep j
      have hwide : (a j-1)+2 ≤ (c j.succ).val-(c j.castSucc).val := by dsimp [a] at *; omega
      have hn : a j-1 < N+1 := by dsimp [a] at *; omega
      have hqn : Q (a j-1) ≤ T := Finset.le_sup (f := Q) (Finset.mem_range.mpr hn)
      exact ⟨R (a j-1),h (a j-1) K N C (c j.castSucc) (c j.succ) hwide (hsort j) (hqn.trans_lt hq)⟩
    · intro j hj s hs
      apply C.profileInterval_empty (c j.castSucc) (c j.succ) _ s hs
      dsimp [a] at hj
      omega
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}
lemma ext_top_stage (C D : ResidueChamber (K := K) (N := N))
    (ht : C.top = D.top) (hs : ∀ r, C.stage r = D.stage r) : C = D := by
  cases C
  cases D
  cases ht
  have he := funext hs
  cases he
  rfl

theorem exists_unscale (C : ResidueChamber (K := K) (N := N))
    (P : Submodule K[X] (V K N)) (hP : HasPivots P) (u : ℕ)
    (ht : C.top = powerShift P u) :
    ∃ E : ResidueChamber (K := K) (N := N), E.top = P ∧ E.scale u = C := by
  let A : Fin (N+1) → Submodule K[X] (V K N) := fun r => (C.stage r).comap (powerLinear u)
  have hm (r) : powerShift (A r) u = C.stage r := by
    apply Submodule.map_comap_eq_self
    apply (C.profile_stage_le_top r).trans
    rw [ht]
    rintro v ⟨w,hw,rfl⟩
    exact ⟨w,rfl⟩
  have hl (r) : powerShift P 1 ≤ A r := by
    apply Submodule.map_le_iff_le_comap.mp
    change powerShift (powerShift P 1) u ≤ C.stage r
    rw [powerShift_add,show 1+u=u+1 by omega,← powerShift_add,← ht]
    exact C.lower r
  have ha (r) : HasPivots (A r) := by
    intro i
    obtain ⟨n,v,hv,hvlead⟩ := powerShift_hasPivots P hP 1 i
    exact ⟨n,v,hl r hv,hvlead⟩
  let E : ResidueChamber (K := K) (N := N) := {
    top := P
    hasTop := hP
    stage := A
    hasStage := ha
    strict := by
      intro r s hrs
      apply lt_of_le_of_ne (Submodule.comap_mono (C.strict hrs).le)
      intro he
      have hh := congrArg (fun B => powerShift B u) he
      rw [hm,hm] at hh
      exact (C.strict hrs).ne hh
    initial := by
      dsimp [A]
      rw [C.initial,ht]
      exact Submodule.comap_map_eq_of_injective (powerLinear_injective u) P
    lower := hl }
  refine ⟨E,rfl,ext_top_stage _ _ ht.symm ?_⟩
  exact hm
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

end

end OAI
