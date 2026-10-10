import OAI.Computability.MeanPayoff.CountedTraversal

namespace OAI

section

namespace MeanPayoff

def SolveBox.repeatedCounted {n Bmax : ℕ} (I : SolveBox n Bmax)
    (t : Counted (BoxVector I)) (J : ℕ) : Counted (BoxVector I) :=
  (Counted.trials t J).map I.medianBox

namespace CountedAlgorithm

abbrev LowerSolver {n Bmax : ℕ} (P : Budgets n) :=
  (Q : Budgets n) → parameterRank Q.parameter < parameterRank P.parameter →
    (I : SolveBox n Bmax) → Counted (BoxVector I)

def centerUpdate {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (q : BoxVector I) : Counted (BoxVector I) :=
  let K := I.narrowCentered hB q.val
  (K.repeatedCounted (lower P.reduceK (P.reduceK_rank hR) K) (globalJ n Bmax)).bind fun r₁ =>
  (K.repeatedCounted (lower P.reduceM (P.reduceM_rank hR) K) (globalJ n Bmax)).map fun r₂ =>
    I.averageClipped r₁.val r₂.val

def centerSteps {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) :
    ℕ → BoxVector I → Counted (List (BoxVector I))
  | 0, q => Counted.pure [q]
  | t + 1, q =>
    (centerUpdate P hR lower I hB q).bind fun q' =>
    (centerSteps P hR lower I hB t q').map (q :: ·)

def orientationTail (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax)
    (qs : List (BoxVector I)) (child : BoxVector I → Counted (Orientation P)) :
    Counted (Orientation P) :=
  let H := PositiveDisplacement I (qs.getD (globalS Bmax) I.midpoint)
  let N := NegativeDisplacement I (qs.getD (globalS Bmax) I.midpoint)
  if hH : 1 / 2 < P.measure H then
    Counted.pure ⟨true, [⟨Hᶜ, by rw [P.measure_compl G.positive]; linarith⟩]⟩
  else if hN : 1 / 2 < P.measure N then
    Counted.pure ⟨false, [⟨Nᶜ, by rw [P.measure_compl G.positive]; linarith⟩]⟩
  else
    (Counted.lift (RandomTree.uniformBelow (sampleExponent Bmax))).bind fun j =>
      (child (qs.getD j I.midpoint)).map fun O =>
        ⟨O.chooseY, O.exceptions ++ [⟨H, le_of_not_gt hH⟩, ⟨N, le_of_not_gt hN⟩]⟩

def orient (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax) :
    Counted (Orientation P) :=
  if hB : I.width ≤ 128 * globalS Bmax then
    Counted.pure (orientBase G P I)
  else
    let hb : 128 * globalS Bmax < I.width := lt_of_not_ge hB
    (centerSteps P hR lower I hb (globalS Bmax) I.midpoint).bind fun qs =>
      orientationTail G P I qs (fun q => orient G P hR lower (I.wideCentered hb q.val))
termination_by I.width
decreasing_by exact I.E_smaller

def orientPlus {n : ℕ} {P : Budgets n} (t : Counted (Orientation P)) (J : ℕ) :
    Counted (Orientation P) :=
  (Counted.trials t J).map combineOrientations

def tighten {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) : Counted (InnerBox I) :=
  (I.repeatedCounted (lower P.reduceK (P.reduceK_rank hR) I) (globalJ n Bmax)).bind fun r₁ =>
  if _h₁ : ∃ i, (I.delta : ℤ) ≤ r₁.val i - I.a i then
    let K := I.withFloor r₁
    (tighten P hR lower K hB).map fun T =>
      ⟨T.box, T.width_eq, r₁.property.1.trans T.floor_le, T.ceiling_le⟩
  else
    (I.repeatedCounted (lower P.reduceM (P.reduceM_rank hR) I) (globalJ n Bmax)).bind fun r₂ =>
    if _h₂ : ∃ i, (I.delta : ℤ) ≤ I.b i - r₂.val i then
      let K := I.withCeiling r₂
      (tighten P hR lower K hB).map fun T =>
        ⟨T.box, T.width_eq, T.floor_le, T.ceiling_le.trans r₂.property.2⟩
    else Counted.pure ⟨I, rfl, le_refl _, le_refl _⟩
termination_by volume I.b I.a
decreasing_by
  · apply volume_decreases r₁.property.1 r₁.property.2
    obtain ⟨i, hi⟩ := _h₁
    have hd := I.delta_positive hB
    intro heq
    have he := congrFun heq i
    omega
  · apply volume_ceiling_decreases r₂.property.1 r₂.property.2
    obtain ⟨i, hi⟩ := _h₂
    have hd := I.delta_positive hB
    intro heq
    have he := congrFun heq i
    omega

def finishChoice (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax)
    (hB : 128 * globalS Bmax < I.width) (O : Orientation P)
    (up : Counted (BoxVector (I.capHigh I.C I.C_positive (I.C_smaller hB).le)))
    (lo : Counted (BoxVector (I.capLow I.C I.C_positive (I.C_smaller hB).le))) :
    Counted (BoxVector I) :=
  if O.chooseY then
    (Counted.traverse (fun H : SmallSet P =>
      I.repeatedCounted (lower (P.reweightM H.val)
        (P.reweightM_rank G.positive hR H.property) I) (globalJ G.n Bmax)) O.exceptions).bind fun rs =>
    up.map fun p => rs.foldl I.minVector (I.includeCapHigh I.C I.C_positive (I.C_smaller hB).le p)
  else
    (Counted.traverse (fun H : SmallSet P =>
      I.repeatedCounted (lower (P.reweightK H.val)
        (P.reweightK_rank G.positive hR H.property) I) (globalJ G.n Bmax)) O.exceptions).bind fun rs =>
    lo.map fun p => rs.foldl I.maxVector (I.includeCapLow I.C I.C_positive (I.C_smaller hB).le p)

def solveWidth (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax) : Counted (BoxVector I) :=
  Counted.charge 1 <|
  if hB : I.width ≤ 128 * globalS Bmax then Counted.pure (I.exactVector G)
  else
    (tighten P hR lower I (lt_of_not_ge hB)).bind fun T =>
    let K := T.box
    have hK : 128 * globalS Bmax < K.width := by rw [T.width_eq]; omega
    let c := K.C
    have hc : 0 < c := K.C_positive
    have hcsmall : c < K.width := K.C_smaller hK
    (orientPlus (orient G P hR lower K) (globalJ G.n Bmax)).bind fun O =>
    (finishChoice G P hR lower K hK O
      (solveWidth G P hR lower (K.capHigh c hc hcsmall.le))
      (solveWidth G P hR lower (K.capLow c hc hcsmall.le))).map T.include
termination_by I.width
decreasing_by
  all_goals
    change c < I.width
    rw [← T.width_eq]
    exact hcsmall

def solve (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax) :
    Counted (BoxVector I) :=
  if hR : P.parameter < 1 then Counted.charge 1 (Counted.pure (I.smallVector P))
  else solveWidth G P (le_of_not_gt hR) (fun Q _ K => solve G Q K) I
termination_by parameterRank P.parameter

end CountedAlgorithm


@[simp] theorem SolveBox.erase_repeated {n Bmax : ℕ} (I : SolveBox n Bmax)
    (t : Counted (BoxVector I)) (J : ℕ) :
    (I.repeatedCounted t J).erase = I.repeated t.erase J := by
  simp [SolveBox.repeatedCounted, SolveBox.repeated]

theorem SolveBox.bounded_repeated {n Bmax : ℕ} (I : SolveBox n Bmax)
    {t : Counted (BoxVector I)} {N : ℕ} (h : t.Bounded N) (J : ℕ) :
    (I.repeatedCounted t J).Bounded (J * N) :=
  Counted.bounded_map _ (Counted.bounded_trials h J)

namespace CountedAlgorithm

def eraseLower {n Bmax : ℕ} {P : Budgets n} (lower : LowerSolver (Bmax := Bmax) P) :
    MeanPayoff.LowerSolver (Bmax := Bmax) P := fun Q h I => (lower Q h I).erase

abbrev LowerBound {n Bmax : ℕ} {P : Budgets n} (lower : LowerSolver (Bmax := Bmax) P)
    (N : ℕ) : Prop := ∀ Q h I, (lower Q h I).Bounded N

@[simp] theorem erase_centerUpdate {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (q : BoxVector I) :
    (centerUpdate P hR lower I hB q).erase =
    MeanPayoff.centerUpdate P hR (eraseLower lower) I hB q := by
  simp [centerUpdate, MeanPayoff.centerUpdate, eraseLower]

@[simp] theorem erase_centerSteps {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (t : ℕ) (q : BoxVector I) :
    (centerSteps P hR lower I hB t q).erase =
    MeanPayoff.centerSteps P hR (eraseLower lower) I hB t q := by
  induction t generalizing q with
  | zero => rfl
  | succ t ih => simp only [centerSteps, MeanPayoff.centerSteps, Counted.erase_bind,
      erase_centerUpdate, Counted.erase_map, ih]

@[simp] theorem erase_orientationTail (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (I : SolveBox G.n Bmax) (qs : List (BoxVector I))
    (child : BoxVector I → Counted (Orientation P)) :
    (orientationTail G P I qs child).erase =
    MeanPayoff.orientationTail G P I qs (fun q => (child q).erase) := by
  unfold orientationTail MeanPayoff.orientationTail
  dsimp only
  split_ifs <;> simp

@[simp] theorem erase_orient (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax) :
    (orient G P hR lower I).erase = MeanPayoff.orient G P hR (eraseLower lower) I := by
  rw [orient, MeanPayoff.orient]
  split_ifs with h
  · rfl
  · simp only [Counted.erase_bind, erase_centerSteps, erase_orientationTail]
    apply congrArg (RandomTree.bind _)
    funext qs
    apply congrArg (MeanPayoff.orientationTail G P I qs)
    funext q
    exact erase_orient G P hR lower (I.wideCentered (lt_of_not_ge h) q.val)
termination_by I.width
 decreasing_by exact I.E_smaller

@[simp] theorem erase_orientPlus {n : ℕ} {P : Budgets n}
    (t : Counted (Orientation P)) (J : ℕ) :
    (orientPlus t J).erase = MeanPayoff.orientPlus t.erase J := by
  simp [orientPlus, MeanPayoff.orientPlus]

@[simp] theorem erase_tighten {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) :
    (tighten P hR lower I hB).erase = MeanPayoff.tighten P hR (eraseLower lower) I hB := by
  rw [tighten, MeanPayoff.tighten]
  simp only [Counted.erase_bind, SolveBox.erase_repeated]
  congr 1
  funext r₁
  split_ifs with h₁
  · simp only [Counted.erase_map, erase_tighten P hR lower (I.withFloor r₁) hB]
  · simp only [Counted.erase_bind, SolveBox.erase_repeated]
    congr 1
    funext r₂
    split_ifs with h₂
    · simp only [Counted.erase_map, erase_tighten P hR lower (I.withCeiling r₂) hB]
    · rfl
termination_by volume I.b I.a
 decreasing_by
  · apply volume_decreases r₁.property.1 r₁.property.2
    obtain ⟨i, hi⟩ := h₁
    have hd := I.delta_positive hB
    intro heq
    have he := congrFun heq i
    omega
  · apply volume_ceiling_decreases r₂.property.1 r₂.property.2
    obtain ⟨i, hi⟩ := h₂
    have hd := I.delta_positive hB
    intro heq
    have he := congrFun heq i
    omega

@[simp] theorem erase_finishChoice (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (hR : 1 ≤ P.parameter) (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax)
    (hB : 128 * globalS Bmax < I.width) (O : Orientation P)
    (up : Counted (BoxVector (I.capHigh I.C I.C_positive (I.C_smaller hB).le)))
    (lo : Counted (BoxVector (I.capLow I.C I.C_positive (I.C_smaller hB).le))) :
    (finishChoice G P hR lower I hB O up lo).erase =
    MeanPayoff.finishChoice G P hR (eraseLower lower) I hB O up.erase lo.erase := by
  unfold finishChoice MeanPayoff.finishChoice
  split_ifs <;> simp [eraseLower]

@[simp] theorem erase_solveWidth (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (hR : 1 ≤ P.parameter) (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax) :
    (solveWidth G P hR lower I).erase = MeanPayoff.solveWidth G P hR (eraseLower lower) I := by
  rw [solveWidth, MeanPayoff.solveWidth, Counted.erase_charge]
  split_ifs with hB
  · rfl
  · simp only [Counted.erase_bind, erase_tighten]
    congr 1
    funext T
    simp only [erase_orientPlus, erase_orient]
    congr 1
    funext O
    simp only [Counted.erase_map, erase_finishChoice]
    congr 2
    · exact erase_solveWidth G P hR lower _
    · exact erase_solveWidth G P hR lower _
termination_by I.width
 decreasing_by
  all_goals
    change T.box.C < I.width
    rw [← T.width_eq]
    exact T.box.C_smaller (by rw [T.width_eq]; omega)

@[simp] theorem erase_solve (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax) :
    (solve G P I).erase = MeanPayoff.solve G P I := by
  rw [solve, MeanPayoff.solve]
  split_ifs with hR
  · rfl
  · rw [erase_solveWidth]
    congr 1
    funext Q h K
    exact erase_solve G Q K
termination_by parameterRank P.parameter

end CountedAlgorithm
end MeanPayoff
end

end OAI
