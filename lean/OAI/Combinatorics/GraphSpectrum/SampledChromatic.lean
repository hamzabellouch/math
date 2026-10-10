import Mathlib

namespace OAI

/-! Colin de Verdiere matrix definitions and chromatic bounds for graphs sampled from a binary hole relation. -/

namespace CdV

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

def WellSigned (G : SimpleGraph V) (M : Matrix V V ℝ) : Prop :=
  M.IsSymm ∧ ∀ i j, i ≠ j →
    (G.Adj i j → M i j < 0) ∧ (¬G.Adj i j → M i j = 0)

def OneNegativeEigenvalue (M : Matrix V V ℝ) : Prop := by
  classical
  exact ∃ hM : M.IsHermitian,
    Fintype.card {i : V // hM.eigenvalues i < 0} = 1

def StrongArnold (G : SimpleGraph V) (M : Matrix V V ℝ) : Prop :=
  ∀ X : Matrix V V ℝ, X.IsSymm → M * X = 0 →
    (∀ i, X i i = 0) → (∀ i j, G.Adj i j → X i j = 0) → X = 0

noncomputable def nullity (M : Matrix V V ℝ) : ℕ :=
  Module.finrank ℝ (LinearMap.ker M.mulVecLin)

def Admissible (G : SimpleGraph V) (M : Matrix V V ℝ) : Prop :=
  WellSigned G M ∧ OneNegativeEigenvalue M ∧ StrongArnold G M

def admissibleNullities (G : SimpleGraph V) : Set ℕ :=
  {k | ∃ M : Matrix V V ℝ, Admissible G M ∧ nullity M = k}

noncomputable def mu (G : SimpleGraph V) : ℕ := sSup (admissibleNullities G)

noncomputable def chi (G : SimpleGraph V) : ℕ := G.chromaticNumber.toNat

def ChromaticConjecture : Prop :=
  ∀ n : ℕ, 0 < n → ∀ G : SimpleGraph (Fin n), chi G ≤ mu G + 1

omit [DecidableEq V] in
lemma rank_add_nullity (M : Matrix V V ℝ) :
    M.rank + nullity M = Fintype.card V := by
  simpa [Matrix.rank, nullity] using M.mulVecLin.finrank_range_add_finrank_ker

omit [DecidableEq V] in
lemma nullity_le_card (M : Matrix V V ℝ) : nullity M ≤ Fintype.card V := by
  have := rank_add_nullity M
  omega

lemma admissibleNullities_bddAbove (G : SimpleGraph V) :
    BddAbove (admissibleNullities G) := by
  refine ⟨Fintype.card V, ?_⟩
  rintro k ⟨M, _, rfl⟩
  exact nullity_le_card M

lemma nullity_le_mu {G : SimpleGraph V} {M : Matrix V V ℝ}
    (hM : Admissible G M) : nullity M ≤ mu G := by
  exact le_csSup (admissibleNullities_bddAbove G) ⟨M, hM, rfl⟩

lemma mu_le_card (G : SimpleGraph V) : mu G ≤ Fintype.card V := by
  apply csSup_le'
  rintro k ⟨M, _, rfl⟩
  exact nullity_le_card M

lemma exists_nullity_eq_mu {G : SimpleGraph V}
    (hG : ∃ M, Admissible G M) :
    ∃ M, Admissible G M ∧ nullity M = mu G := by
  apply Nat.sSup_mem _ (admissibleNullities_bddAbove G)
  obtain ⟨M, hM⟩ := hG
  exact ⟨nullity M, M, hM, rfl⟩

lemma strongArnold_of_isUnit {G : SimpleGraph V} {M : Matrix V V ℝ}
    (hM : IsUnit M) : StrongArnold G M := by
  intro X _ hMX _ _
  obtain ⟨U, rfl⟩ := hM
  have h := congrArg (fun A : Matrix V V ℝ => (↑U⁻¹ : Matrix V V ℝ) * A) hMX
  simpa [← mul_assoc] using h

omit [DecidableEq V] in

private lemma neg_card_of_trace (f : V → ℝ) (c R : ℝ)
    (hc : 0 < c) (hmargin : (Fintype.card V : ℝ) * R < 2 * c)
    (hnear : ∀ i, |f i - (if f i < 0 then -c else c)| ≤ R)
    (hsum : ∑ i, f i = (Fintype.card V : ℝ) * c - 2 * c) :
    Fintype.card {i : V // f i < 0} = 1 := by
  classical
  let S : Finset V := Finset.univ.filter (fun i => f i < 0)
  have hcenter : (∑ i, if f i < 0 then -c else c) =
      (Fintype.card V : ℝ) * c - 2 * (S.card : ℝ) * c := by
    calc
      _ = ∑ i, (c - if f i < 0 then 2 * c else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> ring
      _ = _ := by
        rw [Finset.sum_sub_distrib]
        simp [S, Finset.sum_ite]
        ring
  have herr : |2 * ((S.card : ℝ) - 1) * c| < 2 * c := by
    calc
      _ = |∑ i, (f i - (if f i < 0 then -c else c))| := by
        rw [Finset.sum_sub_distrib, hsum, hcenter]
        congr 1
        ring
      _ ≤ ∑ i, |f i - (if f i < 0 then -c else c)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : V, R := Finset.sum_le_sum fun i _ => hnear i
      _ = (Fintype.card V : ℝ) * R := by simp
      _ < 2 * c := hmargin
  have hb := abs_lt.mp herr
  have hlo : 0 < (S.card : ℝ) := by nlinarith
  have hhi : (S.card : ℝ) < 2 := by nlinarith
  have hpos : 0 < S.card := by exact_mod_cast hlo
  have hlt : S.card < 2 := by exact_mod_cast hhi
  have hcard : S.card = 1 := by omega
  simpa [S, Fintype.card_subtype] using hcard

noncomputable def seedMatrix (G : SimpleGraph V) (v : V) (c : ℝ) : Matrix V V ℝ := by
  classical
  exact Matrix.diagonal (fun i => if i = v then -c else c) - G.adjMatrix ℝ

omit [Fintype V] in
lemma seedMatrix_isSymm (G : SimpleGraph V) (v : V) (c : ℝ) :
    (seedMatrix G v c).IsSymm := by
  classical
  exact (Matrix.isSymm_diagonal _).sub (G.isSymm_adjMatrix)

omit [Fintype V] in
lemma seedMatrix_diag (G : SimpleGraph V) (v i : V) (c : ℝ) :
    seedMatrix G v c i i = if i = v then -c else c := by
  classical
  simp [seedMatrix, SimpleGraph.adjMatrix_apply]

open scoped Classical in
omit [Fintype V] in
lemma seedMatrix_offDiag (G : SimpleGraph V) (v i j : V) (c : ℝ) (hij : i ≠ j) :
    seedMatrix G v c i j = if G.Adj i j then -1 else 0 := by
  classical
  simp only [seedMatrix, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij,
    SimpleGraph.adjMatrix_apply, zero_sub]
  split_ifs <;> norm_num

lemma seedMatrix_offDiag_norm_sum (G : SimpleGraph V) (v i : V) (c : ℝ) :
    (∑ j ∈ Finset.univ.erase i, ‖seedMatrix G v c i j‖) ≤ Fintype.card V := by
  classical
  calc
    _ ≤ ∑ _j ∈ Finset.univ.erase i, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [seedMatrix_offDiag G v i j c (Finset.ne_of_mem_erase hj).symm]
      split_ifs <;> norm_num
    _ = ((Finset.univ.erase i).card : ℝ) := by simp
    _ ≤ (Fintype.card V : ℝ) := by exact_mod_cast Finset.card_le_card (Finset.erase_subset i Finset.univ)

lemma seedMatrix_trace (G : SimpleGraph V) (v : V) (c : ℝ) :
    Matrix.trace (seedMatrix G v c) = (Fintype.card V : ℝ) * c - 2 * c := by
  classical
  calc
    _ = ∑ i, (c - if i = v then 2 * c else 0) := by
      unfold Matrix.trace Matrix.diag
      apply Finset.sum_congr rfl
      intro i _
      rw [seedMatrix_diag]
      split_ifs <;> ring
    _ = _ := by rw [Finset.sum_sub_distrib]; simp

lemma seedMatrix_neg_eigenvalues (G : SimpleGraph V) (v : V) {c : ℝ}
    (hc : (Fintype.card V : ℝ) < c)
    (hmargin : (Fintype.card V : ℝ) ^ 2 < 2 * c) :
    let hM : (seedMatrix G v c).IsHermitian :=
      Matrix.isHermitian_iff_isSymm.mpr (seedMatrix_isSymm G v c)
    Fintype.card {i : V // hM.eigenvalues i < 0} = 1 := by
  classical
  intro hM
  apply neg_card_of_trace hM.eigenvalues c (Fintype.card V)
  · exact lt_of_le_of_lt (Nat.cast_nonneg _) hc
  · nlinarith
  · intro i
    have heig : Module.End.HasEigenvalue (Matrix.toLin' (seedMatrix G v c)) (hM.eigenvalues i) := by
      apply Module.End.HasEigenvalue.of_mem_spectrum
      rw [Matrix.spectrum_toLin']
      exact hM.eigenvalues_mem_spectrum_real i
    obtain ⟨k, hk⟩ := eigenvalue_mem_ball heig
    have hk' : |hM.eigenvalues i - (if k = v then -c else c)| ≤ Fintype.card V := by
      have h := hk.trans (seedMatrix_offDiag_norm_sum G v k c)
      simpa only [Metric.mem_closedBall, Real.dist_eq, seedMatrix_diag] using h
    by_cases hkv : k = v
    · simp only [hkv, ite_true] at hk'
      have hneg : hM.eigenvalues i < 0 := by
        have := (abs_le.mp hk').2
        linarith
      simpa only [hneg, ite_true] using hk'
    · simp only [hkv, ite_false] at hk'
      have hpos : ¬ hM.eigenvalues i < 0 := by
        have := (abs_le.mp hk').1
        linarith
      simpa only [hpos, ite_false] using hk'
  · have ht : Matrix.trace (seedMatrix G v c) = ∑ i, hM.eigenvalues i := by
      simpa using hM.trace_eq_sum_eigenvalues
    rw [← ht]
    exact seedMatrix_trace G v c

lemma seedMatrix_isUnit (G : SimpleGraph V) (v : V) {c : ℝ}
    (hc : (Fintype.card V : ℝ) < c) : IsUnit (seedMatrix G v c) := by
  classical
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  apply det_ne_zero_of_sum_row_lt_diag
  intro i
  apply lt_of_le_of_lt (seedMatrix_offDiag_norm_sum G v i c)
  rw [seedMatrix_diag]
  split_ifs <;> simpa [abs_of_pos (lt_of_le_of_lt (Nat.cast_nonneg _) hc)] using hc

lemma exists_admissible [Nonempty V] (G : SimpleGraph V) :
    ∃ M : Matrix V V ℝ, Admissible G M := by
  classical
  let v : V := Classical.arbitrary V
  let c : ℝ := (Fintype.card V : ℝ) ^ 2 + 1
  have hc : (Fintype.card V : ℝ) < c := by
    dsimp [c]
    nlinarith [sq_nonneg ((Fintype.card V : ℝ) - 1 / 2)]
  have hmargin : (Fintype.card V : ℝ) ^ 2 < 2 * c := by
    dsimp [c]
    nlinarith [sq_nonneg (Fintype.card V : ℝ)]
  refine ⟨seedMatrix G v c, ?_, ?_, ?_⟩
  · refine ⟨seedMatrix_isSymm G v c, ?_⟩
    intro i j hij
    rw [seedMatrix_offDiag G v i j c hij]
    constructor
    · intro h; simp [h]
    · intro h; simp [h]
  · refine ⟨Matrix.isHermitian_iff_isSymm.mpr (seedMatrix_isSymm G v c), ?_⟩
    exact seedMatrix_neg_eigenvalues G v hc hmargin
  · exact strongArnold_of_isUnit (seedMatrix_isUnit G v hc)

lemma admissibleNullities_nonempty [Nonempty V] (G : SimpleGraph V) :
    (admissibleNullities G).Nonempty := by
  obtain ⟨M, hM⟩ := exists_admissible G
  exact ⟨nullity M, M, hM, rfl⟩

lemma exists_maximizing_admissible [Nonempty V] (G : SimpleGraph V) :
    ∃ M, Admissible G M ∧ nullity M = mu G :=
  exists_nullity_eq_mu (exists_admissible G)

def RankObstruction (G : SimpleGraph V) : Prop :=
  ∀ M : Matrix V V ℝ, WellSigned G M → OneNegativeEigenvalue M →
    (Fintype.card V : ℝ) / 2 + 1 < (M.rank : ℝ)

lemma mu_gap_of_rankObstruction [Nonempty V] {G : SimpleGraph V}
    (hrank : RankObstruction G) :
    (mu G : ℝ) + 1 < (Fintype.card V : ℝ) / 2 := by
  obtain ⟨M, hM, hnull⟩ := exists_maximizing_admissible G
  have hR := hrank M hM.1 hM.2.1
  have hdim : (M.rank : ℝ) + (nullity M : ℝ) = (Fintype.card V : ℝ) := by
    exact_mod_cast rank_add_nullity M
  rw [hnull] at hdim
  linarith

omit [DecidableEq V] in
lemma chi_colorable (G : SimpleGraph V) : G.Colorable (chi G) :=
  G.colorable_chromaticNumber_of_fintype

omit [DecidableEq V] in

lemma card_le_indepNum_mul_chi (G : SimpleGraph V) :
    Fintype.card V ≤ G.indepNum * chi G := by
  classical
  obtain ⟨C⟩ := chi_colorable G
  have hfiber (c : Fin (chi G)) :
      Fintype.card {v : V // C v = c} ≤ G.indepNum := by
    have hind : G.IsIndepSet ((Finset.univ.filter (fun v : V => C v = c)) : Set V) := by
      intro v hv w hw _
      exact C.not_adj_of_mem_colorClass (Finset.mem_filter.mp hv).2
        (Finset.mem_filter.mp hw).2
    simpa [Fintype.card_subtype] using hind.card_le_indepNum
  calc
    Fintype.card V = Fintype.card (Σ c : Fin (chi G), {v : V // C v = c}) :=
      Fintype.card_congr (Equiv.sigmaFiberEquiv C).symm
    _ = ∑ c : Fin (chi G), Fintype.card {v : V // C v = c} := Fintype.card_sigma
    _ ≤ ∑ _c : Fin (chi G), G.indepNum := Finset.sum_le_sum fun c _ => hfiber c
    _ = G.indepNum * chi G := by simp [Nat.mul_comm]

omit [DecidableEq V] in
lemma half_order_le_chi {G : SimpleGraph V} (hα : G.indepNum ≤ 2) :
    (Fintype.card V : ℝ) / 2 ≤ (chi G : ℝ) := by
  have h : Fintype.card V ≤ 2 * chi G :=
    (card_le_indepNum_mul_chi G).trans (Nat.mul_le_mul_right _ hα)
  have hR : (Fintype.card V : ℝ) ≤ 2 * (chi G : ℝ) := by exact_mod_cast h
  linarith

omit [Fintype V] [DecidableEq V] in
lemma indepNum_le_two_of_no_independent_triple (G : SimpleGraph V)
    (hG : ∀ a b c : V, a ≠ b → a ≠ c → b ≠ c →
      ¬ G.Adj a b → ¬ G.Adj a c → ¬ G.Adj b c → False) :
    G.indepNum ≤ 2 := by
  obtain ⟨S, hS⟩ := G.exists_isNIndepSet_indepNum
  rw [← hS.card_eq]
  by_contra h
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp (Nat.lt_of_not_ge h)
  exact hG a b c hab hac hbc (hS.isIndepSet ha hb hab)
    (hS.isIndepSet ha hc hac) (hS.isIndepSet hb hc hbc)

lemma inequalities_of_rankObstruction [Nonempty V] {G : SimpleGraph V}
    (hα : G.indepNum ≤ 2) (hrank : RankObstruction G) :
    (mu G : ℝ) + 1 < (Fintype.card V : ℝ) / 2 ∧
      (Fintype.card V : ℝ) / 2 ≤ (chi G : ℝ) :=
  ⟨mu_gap_of_rankObstruction hrank, half_order_le_chi hα⟩

lemma not_chromaticConjecture_of_gap {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n))
    (hμ : (mu G : ℝ) + 1 < (n : ℝ) / 2)
    (hχ : (n : ℝ) / 2 ≤ (chi G : ℝ)) :
    ¬ ChromaticConjecture := by
  intro hconj
  have h : (chi G : ℝ) ≤ (mu G : ℝ) + 1 := by
    exact_mod_cast hconj n hn G
  linarith

def cliqueBlowup (H : SimpleGraph V) (s : ℕ) : SimpleGraph (V × Fin s) where
  Adj p q := p ≠ q ∧ (p.1 = q.1 ∨ H.Adj p.1 q.1)
  symm := ⟨by
    intro p q hpq
    exact ⟨hpq.1.symm, hpq.2.elim (fun h => Or.inl h.symm)
      (fun h => Or.inr h.symm)⟩⟩
  loopless := ⟨by intro p hp; exact hp.1 rfl⟩

lemma indepNum_cliqueBlowup_le (H : SimpleGraph V) (s : ℕ) :
    (cliqueBlowup H s).indepNum ≤ H.indepNum := by
  classical
  obtain ⟨S, hS⟩ := (cliqueBlowup H s).exists_isNIndepSet_indepNum
  have hinj : Set.InjOn Prod.fst (S : Set (V × Fin s)) := by
    intro p hp q hq heq
    by_contra hne
    exact hS.isIndepSet hp hq hne ⟨hne, Or.inl heq⟩
  have hproj : H.IsIndepSet (S.image Prod.fst : Set V) := by
    intro v hv w hw hvw hvwAdj
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hw
    have hpq : p ≠ q := fun h => hvw (congrArg Prod.fst h)
    exact hS.isIndepSet hp hq hpq ⟨hpq, Or.inr hvwAdj⟩
  calc
    (cliqueBlowup H s).indepNum = S.card := hS.card_eq.symm
    _ = (S.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ H.indepNum := hproj.card_le_indepNum

lemma indepNum_cliqueBlowup (H : SimpleGraph V) {s : ℕ} (hs : 0 < s) :
    (cliqueBlowup H s).indepNum = H.indepNum := by
  classical
  apply le_antisymm (indepNum_cliqueBlowup_le H s)
  obtain ⟨S, hS⟩ := H.exists_isNIndepSet_indepNum
  let f : V → V × Fin s := fun v => (v, ⟨0, hs⟩)
  have hf : Function.Injective f := fun v w h => congrArg Prod.fst h
  have hind : (cliqueBlowup H s).IsIndepSet (S.image f : Set (V × Fin s)) := by
    intro p hp q hq hpq hadj
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
    have hvw : v ≠ w := fun h => hpq (congrArg f h)
    rcases hadj.2 with heq | hedge
    · exact hvw heq
    · exact hS.isIndepSet hv hw hvw hedge
  calc
    H.indepNum = S.card := hS.card_eq.symm
    _ = (S.image f).card := (Finset.card_image_of_injective S hf).symm
    _ ≤ (cliqueBlowup H s).indepNum := hind.card_le_indepNum

lemma cliqueBlowup_independence_and_colouring (H : SimpleGraph V)
    (hH : H.indepNum ≤ 2) (s : ℕ) :
    (cliqueBlowup H s).indepNum ≤ 2 ∧
      (Fintype.card V * s : ℝ) / 2 ≤ (chi (cliqueBlowup H s) : ℝ) := by
  have hα := (indepNum_cliqueBlowup_le H s).trans hH
  refine ⟨hα, ?_⟩
  simpa using half_order_le_chi hα

namespace Geometry

abbrev F := ZMod 2

variable {X A Ω : Type*} [AddCommGroup X] [Module F X]
  [AddCommGroup A] [Module F A]

def Hole (U : Ω → X →ₗ[F] A) (u : Ω → A →ₗ[F] F)
    (a : X →ₗ[F] F) (T : X →ₗ[F] X →ₗ[F] F) (i j : Ω) : Prop :=
  ∃ x y : X, U i x = U j y ∧
    (u j).comp (U i) = a + T x ∧
    (u i).comp (U j) = a + T y ∧
    a x + a y = 1

variable {U : Ω → X →ₗ[F] A} {u : Ω → A →ₗ[F] F}
  {a : X →ₗ[F] F} {T : X →ₗ[F] X →ₗ[F] F}

lemma hole_symm {i j : Ω} (h : Hole U u a T i j) : Hole U u a T j i := by
  obtain ⟨x, y, hxy, hi, hj, hpar⟩ := h
  exact ⟨y, x, hxy.symm, hj, hi, by simpa [add_comm] using hpar⟩

lemma hole_irrefl (hU : ∀ i, Function.Injective (U i)) (i : Ω) :
    ¬ Hole U u a T i i := by
  rintro ⟨x, y, hxy, _, _, hpar⟩
  have h := hU i hxy
  rw [h, CharTwo.add_self_eq_zero] at hpar
  exact zero_ne_one hpar

lemma hole_triangle_free (hT : ∀ x y : X, T x y = T y x)
    (i j k : Ω) (hij : Hole U u a T i j)
    (hik : Hole U u a T i k) (hjk : Hole U u a T j k) : False := by
  obtain ⟨xij, xji, sij, gij, gji, pij⟩ := hij
  obtain ⟨xik, xki, sik, gik, gki, pik⟩ := hik
  obtain ⟨xjk, xkj, sjk, gjk, gkj, pjk⟩ := hjk
  have eval {v w : Ω} {x : X} (h : (u w).comp (U v) = a + T x) (y : X) :
      u w (U v y) = a y + T x y := DFunLike.congr_fun h y
  have e1 : a xik + T xij xik = a xki + T xki xkj := by
    calc
      _ = u j (U i xik) := (eval gij xik).symm
      _ = u j (U k xki) := congrArg (u j) sik
      _ = a xki + T xkj xki := eval gkj xki
      _ = _ := by rw [hT xkj xki]
  have e2 : a xij + T xij xik = a xji + T xji xjk := by
    calc
      _ = a xij + T xik xij := by rw [hT xik xij]
      _ = u k (U i xij) := (eval gik xij).symm
      _ = u k (U j xji) := congrArg (u k) sij
      _ = a xji + T xjk xji := eval gjk xji
      _ = _ := by rw [hT xjk xji]
  have e3 : a xjk + T xji xjk = a xkj + T xki xkj := by
    calc
      _ = u i (U j xjk) := (eval gji xjk).symm
      _ = u i (U k xkj) := congrArg (u i) sjk
      _ = _ := eval gki xkj
  have hbad : (0 : F) = 1 := by
    linear_combination (norm := ring_nf) e1 + e2 + e3 + pij + pik + pjk
    simp [CharTwo.two_eq_zero]
  exact zero_ne_one hbad

def sampledGraph {I : Type*} (U : Ω → X →ₗ[F] A) (u : Ω → A →ₗ[F] F)
    (a : X →ₗ[F] F) (T : X →ₗ[F] X →ₗ[F] F) (sample : I → Ω) : SimpleGraph I where
  Adj i j := i ≠ j ∧ ¬ Hole U u a T (sample i) (sample j)
  symm := ⟨by
    intro i j h
    exact ⟨h.1.symm, fun h' => h.2 (hole_symm h')⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

lemma sampledGraph_adj_of_same_type {I : Type*} (sample : I → Ω)
    (hU : ∀ i, Function.Injective (U i)) {i j : I}
    (hij : i ≠ j) (hsame : sample i = sample j) :
    (sampledGraph U u a T sample).Adj i j := by
  refine ⟨hij, ?_⟩
  rw [hsame]
  exact hole_irrefl hU _

lemma sampledGraph_indepNum_le_two {I : Type*} (sample : I → Ω)
    (hT : ∀ x y : X, T x y = T y x) :
    (sampledGraph U u a T sample).indepNum ≤ 2 := by
  classical
  apply indepNum_le_two_of_no_independent_triple
  intro i j k hij hik hjk hneij hneik hnejk
  have hij' : Hole U u a T (sample i) (sample j) := by
    by_contra h
    exact hneij ⟨hij, h⟩
  have hik' : Hole U u a T (sample i) (sample k) := by
    by_contra h
    exact hneik ⟨hik, h⟩
  have hjk' : Hole U u a T (sample j) (sample k) := by
    by_contra h
    exact hnejk ⟨hjk, h⟩
  exact hole_triangle_free hT _ _ _ hij' hik' hjk'

lemma sampledGraph_half_order_le_chi {I : Type*} [Fintype I] (sample : I → Ω)
    (hT : ∀ x y : X, T x y = T y x) :
    (Fintype.card I : ℝ) / 2 ≤ (chi (sampledGraph U u a T sample) : ℝ) :=
  half_order_le_chi (sampledGraph_indepNum_le_two sample hT)

end Geometry
end CdV

end OAI
