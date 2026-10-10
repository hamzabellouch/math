import OAI.Analysis.SeparableQuotients.CoherentClosures

namespace OAI

namespace SeparableQuotient.PathCoding

open CoherentClosures

section OrderedArray
variable {Γ : Type*} [LinearOrder Γ]

/-- Position of a coordinate in an ordered finite closure; no ordinal label is
stored in the code. -/
def position (s : Finset Γ) (x : Γ) : ℕ := (s.filter (· < x)).card

lemma position_strictMonoOn (s : Finset Γ) : StrictMonoOn (position s) s := by
  intro x hx y _ hxy
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, hz.2.trans hxy⟩
  · intro heq
    have h : x ∈ s.filter (· < y) := Finset.mem_filter.mpr ⟨hx, hxy⟩
    rw [← heq] at h
    exact (lt_irrefl x) (Finset.mem_filter.mp h).2

lemma position_inj {s : Finset Γ} {x y : Γ} (hx : x ∈ s) (hy : y ∈ s)
    (h : position s x = position s y) : x = y :=
  (position_strictMonoOn s).injOn hx hy h

lemma position_align {s t : Finset Γ} {a x : Γ}
    (h : s.filter (· ≤ a) = t.filter (· ≤ a)) (hx : x ≤ a) :
    position s x = position t x := by
  unfold position
  congr 1
  ext z
  constructor <;> intro hz
  · obtain ⟨hz, hzx⟩ := Finset.mem_filter.mp hz
    have hz' : z ∈ s.filter (· ≤ a) :=
      Finset.mem_filter.mpr ⟨hz, hzx.le.trans hx⟩
    rw [h] at hz'
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz').1, hzx⟩
  · obtain ⟨hz, hzx⟩ := Finset.mem_filter.mp hz
    have hz' : z ∈ t.filter (· ≤ a) :=
      Finset.mem_filter.mpr ⟨hz, hzx.le.trans hx⟩
    rw [← h] at hz'
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz').1, hzx⟩

/-- A zero-filled rational array recorded by order positions, including zero values. -/
def arrayCode (s : Finset Γ) (f : Γ →₀ ℚ) : Finset (ℕ × ℚ) :=
  s.image (fun x => (position s x, f x))

lemma arrayCode_match {s t : Finset Γ} {f g : Γ →₀ ℚ}
    (h : arrayCode s f = arrayCode t g) {x : Γ} (hx : x ∈ s) :
    ∃ y ∈ t, position s x = position t y ∧ f x = g y := by
  have hm : (position s x, f x) ∈ arrayCode s f := Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rw [h] at hm
  obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hm
  exact ⟨y, hy, (congrArg Prod.fst heq).symm, (congrArg Prod.snd heq).symm⟩

/-- Position alignment from equal compressed arrays and a shared initial segment. -/
lemma position_alignment {s t : Finset Γ} {a : Γ} {f g : Γ →₀ ℚ}
    (hst : s.filter (· ≤ a) = t.filter (· ≤ a))
    (hf : f.support ⊆ s) (hg : g.support ⊆ t)
    (hfa : ∀ x ∈ f.support, x < a)
    (hcode : arrayCode s f = arrayCode t g) : f = g := by
  have align : ∀ x ∈ s, x ≤ a → x ∈ t ∧ position s x = position t x := by
    intro x hx hxa
    have hm : x ∈ s.filter (· ≤ a) := Finset.mem_filter.mpr ⟨hx, hxa⟩
    rw [hst] at hm
    exact ⟨(Finset.mem_filter.mp hm).1, position_align hst hxa⟩
  have nonzero_align : ∀ x, f x ≠ 0 → f x = g x := by
    intro x hx
    have hfx : x ∈ f.support := Finsupp.mem_support_iff.mpr hx
    obtain ⟨y, hy, hpos, hval⟩ := arrayCode_match hcode (hf hfx)
    obtain ⟨hxt, hpxt⟩ := align x (hf hfx) (hfa x hfx).le
    have heq : x = y := position_inj hxt hy (hpxt.symm.trans hpos)
    simpa [heq] using hval
  ext x
  by_cases hfx : f x = 0
  · by_cases hgx : g x = 0
    · simp [hfx, hgx]
    obtain ⟨y, hy, hpos, hval⟩ := arrayCode_match hcode.symm
      (hg (Finsupp.mem_support_iff.mpr hgx))
    have hfy : f y ≠ 0 := by simpa [← hval] using hgx
    have hys : y ∈ f.support := Finsupp.mem_support_iff.mpr hfy
    obtain ⟨hyt, hpyt⟩ := align y hy (hfa y hys).le
    have heq : x = y := position_inj (hg (Finsupp.mem_support_iff.mpr hgx)) hyt
      (hpos.trans hpyt)
    exact (hfy (heq ▸ hfx)).elim
  · exact nonzero_align x hfx

lemma closure_position_alignment {β γ a : OmegaOne} {p : ℕ} {f g : OmegaOne →₀ ℚ}
    (hβ : a ∈ F β p) (hγ : a ∈ F γ p)
    (hf : f.support ⊆ F β p) (hg : g.support ⊆ F γ p)
    (ha : ∀ x ∈ f.support, x < a)
    (hc : arrayCode (F β p) f = arrayCode (F γ p) g) : f = g :=
  position_alignment (shared_initial_segment β γ a p hβ hγ) hf hg ha hc

end OrderedArray
end SeparableQuotient.PathCoding

namespace SeparableQuotient.PathCoding

open CoherentClosures

abbrev Code := List (ℕ × ℕ × Finset (ℕ × ℚ))

def codeBound : Code → ℕ
  | [] => 0
  | x :: xs => max x.2.1 (codeBound xs)

lemma metadata_le_codeBound {c : Code} {x : ℕ × ℕ × Finset (ℕ × ℚ)}
    (hx : x ∈ c) : x.2.1 ≤ codeBound c := by
  induction c with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with h | h
    · subst x
      exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

/-- An injective code greater than every entry of its final metadata. -/
noncomputable def sigma (c : Code) : ℕ := Nat.pair (Encodable.encode c) (codeBound c + 1)

lemma sigma_injective : Function.Injective sigma := by
  intro c d h
  exact Encodable.encode_injective (Nat.pair_eq_pair.mp h).1

lemma codeBound_lt_sigma (c : Code) : codeBound c < sigma c :=
  (Nat.lt_succ_self _).trans_le (Nat.right_le_pair _ _)

/-- Raw infinite path data, retaining the actual rational pieces, declared
weights and metadata. Nonzero pieces are included here to define the prefix
endpoint without arbitrary defaults. Type-I membership is not needed for the
combinatorial rigidity theorem. -/
@[ext] structure RawPath where
  piece : ℕ → OmegaOne →₀ ℚ
  weight : ℕ → ℕ
  metadata : ℕ → ℕ
  nonzero : ∀ i, piece i ≠ 0

namespace RawPath

noncomputable def support (P : RawPath) (n : ℕ) : Finset OmegaOne :=
  (Finset.range (n+1)).biUnion (fun i => (P.piece i).support)

lemma mem_support_iff (P : RawPath) (n : ℕ) (a : OmegaOne) :
    a ∈ P.support n ↔ ∃ i ≤ n, a ∈ (P.piece i).support := by
  classical
  simp only [support, Finset.mem_biUnion, Finset.mem_range, Nat.lt_succ_iff]

lemma piece_support_subset (P : RawPath) {i n : ℕ} (hi : i ≤ n) :
    (P.piece i).support ⊆ P.support n := by
  intro a ha
  exact (P.mem_support_iff n a).mpr ⟨i, hi, ha⟩

lemma support_nonempty (P : RawPath) (n : ℕ) : (P.support n).Nonempty := by
  obtain ⟨a, ha⟩ := Finsupp.support_nonempty_iff.mpr (P.nonzero n)
  exact ⟨a, P.piece_support_subset le_rfl ha⟩

noncomputable def endpoint (P : RawPath) (n : ℕ) : OmegaOne :=
  (P.support n).max' (P.support_nonempty n)

lemma endpoint_mem (P : RawPath) (n : ℕ) : P.endpoint n ∈ P.support n :=
  Finset.max'_mem _ _

lemma le_endpoint (P : RawPath) {n : ℕ} {a : OmegaOne} (ha : a ∈ P.support n) :
    a ≤ P.endpoint n := Finset.le_max' _ _ ha

noncomputable def closure (P : RawPath) (n : ℕ) : Finset OmegaOne :=
  F (P.endpoint n) (P.metadata n)

noncomputable def code (P : RawPath) (n : ℕ) : Code :=
  List.ofFn (fun i : Fin (n+1) =>
    (P.weight i, P.metadata i, arrayCode (P.closure n) (P.piece i)))

lemma code_length (P : RawPath) (n : ℕ) : (P.code n).length = n+1 :=
  List.length_ofFn

lemma code_eq_length {P Q : RawPath} {n m : ℕ} (h : P.code n = Q.code m) : n = m := by
  have h' := congrArg List.length h
  simpa only [code_length, Nat.add_right_cancel_iff] using h'

lemma code_eq_at {P Q : RawPath} {n : ℕ} (h : P.code n = Q.code n)
    (i : ℕ) (hi : i ≤ n) :
    P.weight i = Q.weight i ∧ P.metadata i = Q.metadata i ∧
      arrayCode (P.closure n) (P.piece i) = arrayCode (Q.closure n) (Q.piece i) := by
  have heq := congrFun (List.ofFn_injective h) ⟨i, Nat.lt_succ_iff.mpr hi⟩
  exact ⟨congrArg Prod.fst heq, congrArg (fun x => x.2.1) heq,
    congrArg (fun x => x.2.2) heq⟩

lemma metadata_le_codeBound (P : RawPath) (n : ℕ) : P.metadata n ≤ codeBound (P.code n) := by
  apply PathCoding.metadata_le_codeBound (x :=
    (P.weight n, P.metadata n, arrayCode (P.closure n) (P.piece n)))
  exact List.mem_ofFn.mpr ⟨⟨n, by omega⟩, rfl⟩

/-- Exact support, succession, weight and metadata conditions of a path. The
Type-I construction contributes only additional restrictions, not needed below. -/
structure Admissible (P : RawPath) : Prop where
  successive : ∀ i j, i < j → ∀ a ∈ (P.piece i).support,
    ∀ b ∈ (P.piece j).support, a < b
  metadata_strict : StrictMono P.metadata
  metadata_pos : ∀ i, 1 ≤ P.metadata i
  weight_pos : ∀ i, 1 ≤ P.weight i
  weight_le_metadata : ∀ i, P.weight i ≤ P.metadata i
  rho_bound : ∀ n a b, a ∈ P.support n → b ∈ P.support n → a ≤ b →
    rho a b ≤ P.metadata n
  rule : ∀ n, P.weight (n+1) = sigma (P.code n)

lemma Admissible.support_subset_closure {P : RawPath} (hP : P.Admissible) (n : ℕ) :
    P.support n ⊆ P.closure n := by
  intro a ha
  exact (rho_le_iff a (P.endpoint n) (P.le_endpoint ha) _ (hP.metadata_pos n)).mp
    (hP.rho_bound n a (P.endpoint n) ha (P.endpoint_mem n) (P.le_endpoint ha))

lemma Admissible.piece_support_subset_closure {P : RawPath} (hP : P.Admissible)
    {i n : ℕ} (hi : i ≤ n) : (P.piece i).support ⊆ P.closure n :=
  (P.piece_support_subset hi).trans (hP.support_subset_closure n)

lemma Admissible.weight_strict {P : RawPath} (hP : P.Admissible) : StrictMono P.weight := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [hP.rule n]
  exact (hP.weight_le_metadata n).trans_lt
    ((P.metadata_le_codeBound n).trans_lt (codeBound_lt_sigma _))

end RawPath
end SeparableQuotient.PathCoding

namespace SeparableQuotient.PathCoding.RawPath

open CoherentClosures

lemma Admissible.large_matching_prefix {P Q : RawPath} (hP : P.Admissible) (hQ : Q.Admissible)
    (hinf : (Set.range P.weight ∩ Set.range Q.weight).Infinite) (N : ℕ) :
    ∃ n ≥ N, P.code n = Q.code n := by
  obtain ⟨w, ⟨⟨k, hk⟩, ⟨l, hl⟩⟩, hw⟩ :=
    hinf.exists_gt (max (P.weight (N+1)) (Q.weight 0))
  have hk' : N+1 < k := hP.weight_strict.lt_iff_lt.mp
    (by rw [hk]; exact (le_max_left _ _).trans_lt hw)
  have hl' : 0 < l := hQ.weight_strict.lt_iff_lt.mp
    (by rw [hl]; exact (le_max_right _ _).trans_lt hw)
  have hcode : P.code (k-1) = Q.code (l-1) := by
    apply sigma_injective
    rw [← hP.rule, ← hQ.rule]
    have hk'' : k-1+1 = k := by omega
    have hl'' : l-1+1 = l := by omega
    rw [hk'', hl'', hk, hl]
  have heq := code_eq_length hcode
  refine ⟨k-1, by omega, ?_⟩
  simpa only [← heq] using hcode

/-- The support of P is order-cofinal below that of Q. -/
def SupportBelow (P Q : RawPath) : Prop :=
  ∀ i a, a ∈ (P.piece i).support →
    ∃ j b, b ∈ (Q.piece j).support ∧ a ≤ b

lemma supportBelow_total (P Q : RawPath) : P.SupportBelow Q ∨ Q.SupportBelow P := by
  classical
  by_cases h : P.SupportBelow Q
  · exact Or.inl h
  · right
    simp only [SupportBelow, not_forall, not_exists, not_and, not_le] at h
    obtain ⟨i, a, ha, h⟩ := h
    intro j b hb
    exact ⟨i, a, ha, (h j b hb).le⟩

lemma Admissible.eq_of_infinite_shared_weights_of_supportBelow {P Q : RawPath}
    (hP : P.Admissible) (hQ : Q.Admissible)
    (hinf : (Set.range P.weight ∩ Set.range Q.weight).Infinite)
    (hPQ : P.SupportBelow Q) : P = Q := by
  apply RawPath.ext
  · funext i
    obtain ⟨a, ha⟩ := Finsupp.support_nonempty_iff.mpr (P.nonzero (i+1))
    obtain ⟨k, b, hb, hab⟩ := hPQ (i+1) a ha
    obtain ⟨n, hn, hcode⟩ := hP.large_matching_prefix hQ hinf (max (i+1) (max k (rho a b)))
    have hin : i ≤ n := by omega
    have hin' : i+1 ≤ n := (le_max_left _ _).trans hn
    have hkn : k ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
    have hrn : rho a b ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
    have hmeta := (code_eq_at hcode n le_rfl).2.1
    have haP : a ∈ P.closure n := hP.piece_support_subset_closure hin' ha
    have hbQ : b ∈ Q.closure n := hQ.piece_support_subset_closure hkn hb
    have haB : a ∈ F b (Q.metadata n) :=
      (rho_le_iff a b hab _ (hQ.metadata_pos n)).mp
        (hrn.trans (hQ.metadata_strict.id_le n))
    have haQ : a ∈ Q.closure n := by
      rw [F_coherent (Q.endpoint n) b (Q.metadata n) hbQ] at haB
      exact (Finset.mem_filter.mp haB).1
    apply position_alignment (a := a)
      (show (P.closure n).filter (· ≤ a) = (Q.closure n).filter (· ≤ a) from ?_)
      (hP.piece_support_subset_closure hin) (hQ.piece_support_subset_closure hin)
      (fun x hx => hP.successive i (i+1) (by omega) x hx a ha)
      (code_eq_at hcode i hin).2.2
    unfold closure at haP ⊢
    rw [hmeta] at haP ⊢
    exact shared_initial_segment (P.endpoint n) (Q.endpoint n) a (Q.metadata n) haP haQ
  · funext i
    obtain ⟨n, hin, hcode⟩ := hP.large_matching_prefix hQ hinf i
    exact (code_eq_at hcode i hin).1
  · funext i
    obtain ⟨n, hin, hcode⟩ := hP.large_matching_prefix hQ hinf i
    exact (code_eq_at hcode i hin).2.1

/-- Distinct admissible paths have only finitely many shared weights. -/
lemma Admissible.eq_of_infinite_shared_weights {P Q : RawPath}
    (hP : P.Admissible) (hQ : Q.Admissible)
    (hinf : (Set.range P.weight ∩ Set.range Q.weight).Infinite) : P = Q := by
  rcases supportBelow_total P Q with h | h
  · exact hP.eq_of_infinite_shared_weights_of_supportBelow hQ hinf h
  · exact (hQ.eq_of_infinite_shared_weights_of_supportBelow hP
      (by simpa only [Set.inter_comm] using hinf) h).symm

lemma Admissible.shared_weights_finite {P Q : RawPath}
    (hP : P.Admissible) (hQ : Q.Admissible) (hne : P ≠ Q) :
    (Set.range P.weight ∩ Set.range Q.weight).Finite := by
  by_contra hinf
  exact hne (hP.eq_of_infinite_shared_weights hQ hinf)

end SeparableQuotient.PathCoding.RawPath

namespace SeparableQuotient.PathCoding.RawPath

/-- A common finite deletion makes the weights of a finite collection of
pairwise distinct paths disjoint. This is the combinatorial input to the
Type-II tail estimate and the quotient-space path map. -/
lemma Admissible.disjoint_weight_tails {ι : Type*} [Fintype ι] (P : ι → RawPath)
    (hP : ∀ i, (P i).Admissible) (hinj : Function.Injective P) :
    ∃ N : ℕ, Pairwise (fun i j => Disjoint
      (Set.range (fun n => (P i).weight (n+N)))
      (Set.range (fun n => (P j).weight (n+N)))) := by
  classical
  have hbound : ∀ i j : ι, ∃ B : ℕ,
      i ≠ j → ∀ n m, (P i).weight n = (P j).weight m → n ≤ B := by
    intro i j
    by_cases hij : i = j
    · exact ⟨0, fun h => (h hij).elim⟩
    · have hfin := (hP i).shared_weights_finite (hP j) (hinj.ne hij)
      obtain ⟨B, hB⟩ := hfin.bddAbove
      refine ⟨B, fun _ n m heq => ?_⟩
      exact ((hP i).weight_strict.id_le n).trans
        (hB ⟨⟨n, rfl⟩, ⟨m, heq.symm⟩⟩)
  choose B hB using hbound
  let N := (Finset.univ : Finset (ι × ι)).sup (fun ij => B ij.1 ij.2) + 1
  refine ⟨N, ?_⟩
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro w ⟨n, hn⟩ ⟨m, hm⟩
  have hnB := hB i j hij (n+N) (m+N) (hn.trans hm.symm)
  have hBN : B i j < N := Nat.lt_succ_of_le
    (Finset.le_sup (f := fun ij : ι × ι => B ij.1 ij.2) (Finset.mem_univ (i,j)))
  omega

end SeparableQuotient.PathCoding.RawPath

end OAI
