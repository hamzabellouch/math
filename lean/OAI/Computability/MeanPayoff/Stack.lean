import OAI.Computability.MeanPayoff.TreeCopy

namespace OAI

section

namespace MeanPayoff
namespace SourceControl

inductive Result (G : Game) (B : ℕ) where
  | vector (I : SolveBox G.n B)
  | vectors (I : SolveBox G.n B)
  | orientation (P : Budgets G.n)
  | orientations (P : Budgets G.n)
  | inner (I : SolveBox G.n B)

abbrev Result.Value {G : Game} {B : ℕ} : Result G B → Type
  | .vector I => BoxVector I
  | .vectors I => List (BoxVector I)
  | .orientation P => Orientation P
  | .orientations P => List (Orientation P)
  | .inner I => InnerBox I

inductive Job (G : Game) (B : ℕ) : Result G B → Type where
  | solve (P : Budgets G.n) (I : SolveBox G.n B) : Job G B (.vector I)
  | ask (P : Budgets G.n) (I : SolveBox G.n B) : Job G B (.vector I)
  | trials (P : Budgets G.n) (I : SolveBox G.n B) (J : ℕ) : Job G B (.vectors I)
  | update (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (hB : 128 * globalS B < I.width) (q : BoxVector I) : Job G B (.vector I)
  | centers (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (hB : 128 * globalS B < I.width) (t : ℕ) (q : BoxVector I) : Job G B (.vectors I)
  | orient (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B) : Job G B (.orientation P)
  | orientTrials (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B) (J : ℕ) :
      Job G B (.orientations P)
  | orientPlus (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B) : Job G B (.orientation P)
  | tighten (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (hB : 128 * globalS B < I.width) : Job G B (.inner I)
  | reweight (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (side : Bool) (Hs : List (SmallSet P)) : Job G B (.vectors I)

inductive Frame (G : Game) (B : ℕ) : Result G B → Result G B → Type where
  | trialsHead (P : Budgets G.n) (I : SolveBox G.n B) (J : ℕ) :
      Frame G B (.vector I) (.vectors I)
  | vectorCons {I : SolveBox G.n B} (a : BoxVector I) :
      Frame G B (.vectors I) (.vectors I)
  | median (I : SolveBox G.n B) : Frame G B (.vectors I) (.vector I)
  | centerFirst (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (hB : 128 * globalS B < I.width) (q : BoxVector I) :
      Frame G B (.vector (I.narrowCentered hB q.val)) (.vector I)
  | centerSecond (I : SolveBox G.n B) (hB : 128 * globalS B < I.width) (q : BoxVector I)
      (r : BoxVector (I.narrowCentered hB q.val)) :
      Frame G B (.vector (I.narrowCentered hB q.val)) (.vector I)
  | centersHead (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (hB : 128 * globalS B < I.width) (t : ℕ) (q : BoxVector I) :
      Frame G B (.vector I) (.vectors I)
  | orientLoop (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (hB : 128 * globalS B < I.width) : Frame G B (.vectors I) (.orientation P)
  | orientTail {P : Budgets G.n} (H N : SmallSet P) : Frame G B (.orientation P) (.orientation P)
  | orientHead (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B) (J : ℕ) :
      Frame G B (.orientation P) (.orientations P)
  | orientCons {P : Budgets G.n} (O : Orientation P) :
      Frame G B (.orientations P) (.orientations P)
  | combine (P : Budgets G.n) : Frame G B (.orientations P) (.orientation P)
  | tightenFirst (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (hB : 128 * globalS B < I.width) : Frame G B (.vector I) (.inner I)
  | tightenSecond (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (hB : 128 * globalS B < I.width) : Frame G B (.vector I) (.inner I)
  | floor (I : SolveBox G.n B) (q : BoxVector I) : Frame G B (.inner (I.withFloor q)) (.inner I)
  | ceiling (I : SolveBox G.n B) (q : BoxVector I) : Frame G B (.inner (I.withCeiling q)) (.inner I)
  | solveTight (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (hB : 128 * globalS B < I.width) : Frame G B (.inner I) (.vector I)
  | solveOriented (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (hB : 128 * globalS B < I.width) : Frame G B (.orientation P) (.vector I)
  | reweightHead (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (side : Bool) (Hs : List (SmallSet P)) : Frame G B (.vector I) (.vectors I)
  | solveReweighted (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (hB : 128 * globalS B < I.width) (side : Bool) : Frame G B (.vectors I) (.vector I)
  | capHigh (I : SolveBox G.n B) (hB : 128 * globalS B < I.width) (rs : List (BoxVector I)) :
      Frame G B (.vector (I.capHigh I.C I.C_positive (I.C_smaller hB).le)) (.vector I)
  | capLow (I : SolveBox G.n B) (hB : 128 * globalS B < I.width) (rs : List (BoxVector I)) :
      Frame G B (.vector (I.capLow I.C I.C_positive (I.C_smaller hB).le)) (.vector I)
  | includeInner {I : SolveBox G.n B} (T : InnerBox I) : Frame G B (.vector T.box) (.vector I)

inductive Kont (G : Game) (B : ℕ) : Result G B → Result G B → Type where
  | done {R : Result G B} : Kont G B R R
  | push {A C R : Result G B} (f : Frame G B A C) (k : Kont G B C R) : Kont G B A R

inductive State (G : Game) (B : ℕ) (R : Result G B) where
  | call {A : Result G B} (j : Job G B A) (k : Kont G B A R)
  | ret {A : Result G B} (k : Kont G B A R) (v : A.Value)

def resume {G : Game} {B : ℕ} {A C R : Result G B} (f : Frame G B A C) (v : A.Value)
    (k : Kont G B C R) : Counted (State G B R) :=
  match f with
  | .trialsHead P I J => Counted.pure (.call (.trials P I J) (.push (.vectorCons v) k))
  | .vectorCons a => Counted.pure (.ret k (a :: v))
  | .median I => Counted.pure (.ret k (I.medianBox v))
  | .centerFirst P _ I hB q =>
      Counted.pure (.call (.ask P.reduceM (I.narrowCentered hB q.val)) (.push (.centerSecond I hB q v) k))
  | .centerSecond I _ _ r => Counted.pure (.ret k (I.averageClipped r.val v.val))
  | .centersHead P hR I hB t q =>
      Counted.pure (.call (.centers P hR I hB t v) (.push (.vectorCons q) k))
  | .orientLoop P hR I hB =>
      let H := PositiveDisplacement I (v.getD (globalS B) I.midpoint)
      let N := NegativeDisplacement I (v.getD (globalS B) I.midpoint)
      if hH : 1 / 2 < P.measure H then
        Counted.pure (.ret k ⟨true, [⟨Hᶜ, by rw [P.measure_compl G.positive]; linarith⟩]⟩)
      else if hN : 1 / 2 < P.measure N then
        Counted.pure (.ret k ⟨false, [⟨Nᶜ, by rw [P.measure_compl G.positive]; linarith⟩]⟩)
      else
        (Counted.lift (RandomTree.uniformBelow (sampleExponent B))).map fun j =>
          .call (.orient P hR (I.wideCentered hB (v.getD j I.midpoint).val))
            (.push (.orientTail ⟨H, le_of_not_gt hH⟩ ⟨N, le_of_not_gt hN⟩) k)
  | .orientTail H N => Counted.pure (.ret k ⟨v.chooseY, v.exceptions ++ [H, N]⟩)
  | .orientHead P hR I J => Counted.pure (.call (.orientTrials P hR I J) (.push (.orientCons v) k))
  | .orientCons O => Counted.pure (.ret k (O :: v))
  | .combine _ => Counted.pure (.ret k (combineOrientations v))
  | .tightenFirst P hR I hB =>
      if _ : ∃ i, (I.delta : ℤ) ≤ v.val i - I.a i then
        Counted.pure (.call (.tighten P hR (I.withFloor v) hB) (.push (.floor I v) k))
      else Counted.pure (.call (.ask P.reduceM I) (.push (.tightenSecond P hR I hB) k))
  | .tightenSecond P hR I hB =>
      if _ : ∃ i, (I.delta : ℤ) ≤ I.b i - v.val i then
        Counted.pure (.call (.tighten P hR (I.withCeiling v) hB) (.push (.ceiling I v) k))
      else Counted.pure (.ret k ⟨I, rfl, le_refl _, le_refl _⟩)
  | .floor _ q => Counted.pure (.ret k ⟨v.box, v.width_eq, q.property.1.trans v.floor_le, v.ceiling_le⟩)
  | .ceiling _ q => Counted.pure (.ret k ⟨v.box, v.width_eq, v.floor_le, v.ceiling_le.trans q.property.2⟩)
  | .solveTight P hR _ hB =>
      have hK : 128 * globalS B < v.box.width := by rw [v.width_eq]; exact hB
      Counted.pure (.call (.orientPlus P hR v.box) (.push (.solveOriented P hR v.box hK) (.push (.includeInner v) k)))
  | .solveOriented P hR I hB =>
      Counted.pure (.call (.reweight P hR I v.chooseY v.exceptions) (.push (.solveReweighted P hR I hB v.chooseY) k))
  | .reweightHead P hR I side Hs => Counted.pure (.call (.reweight P hR I side Hs) (.push (.vectorCons v) k))
  | .solveReweighted P _ I hB side =>
      if side then Counted.pure (.call (.solve P (I.capHigh I.C I.C_positive (I.C_smaller hB).le)) (.push (.capHigh I hB v) k))
      else Counted.pure (.call (.solve P (I.capLow I.C I.C_positive (I.C_smaller hB).le)) (.push (.capLow I hB v) k))
  | .capHigh I hB rs => Counted.pure (.ret k (rs.foldl I.minVector (I.includeCapHigh I.C I.C_positive (I.C_smaller hB).le v)))
  | .capLow I hB rs => Counted.pure (.ret k (rs.foldl I.maxVector (I.includeCapLow I.C I.C_positive (I.C_smaller hB).le v)))
  | .includeInner T => Counted.pure (.ret k (T.include v))

def step {G : Game} {B : ℕ} {R : Result G B} : State G B R → Counted (State G B R)
  | .ret .done v => Counted.pure (.ret .done v)
  | .ret (.push f k) v => resume f v k
  | .call job k => match job with
    | .solve P I => Counted.charge 1 <|
        if hR : P.parameter < 1 then Counted.pure (.ret k (I.smallVector P))
        else if hB : I.width ≤ 128 * globalS B then Counted.pure (.ret k (I.exactVector G))
        else Counted.pure (.call (.tighten P (le_of_not_gt hR) I (by omega)) (.push (.solveTight P (le_of_not_gt hR) I (by omega)) k))
    | .ask P I => Counted.pure (.call (.trials P I (globalJ G.n B)) (.push (.median I) k))
    | .trials P I J => match J with
      | 0 => Counted.pure (.ret k [])
      | J + 1 => Counted.pure (.call (.solve P I) (.push (.trialsHead P I J) k))
    | .update P hR I hB q =>
        Counted.pure (.call (.ask P.reduceK (I.narrowCentered hB q.val)) (.push (.centerFirst P hR I hB q) k))
    | .centers P hR I hB t q => match t with
      | 0 => Counted.pure (.ret k [q])
      | t + 1 => Counted.pure (.call (.update P hR I hB q) (.push (.centersHead P hR I hB t q) k))
    | .orient P hR I =>
        if hB : I.width ≤ 128 * globalS B then Counted.pure (.ret k (orientBase G P I))
        else Counted.pure (.call (.centers P hR I (by omega) (globalS B) I.midpoint) (.push (.orientLoop P hR I (by omega)) k))
    | .orientTrials P hR I J => match J with
      | 0 => Counted.pure (.ret k [])
      | J + 1 => Counted.pure (.call (.orient P hR I) (.push (.orientHead P hR I J) k))
    | .orientPlus P hR I => Counted.pure (.call (.orientTrials P hR I (globalJ G.n B)) (.push (.combine P) k))
    | .tighten P hR I hB => Counted.pure (.call (.ask P.reduceK I) (.push (.tightenFirst P hR I hB) k))
    | .reweight P hR I side Hs => match Hs with
      | [] => Counted.pure (.ret k [])
      | H :: Hs =>
          Counted.pure (.call (.ask (if side then P.reweightM H.val else P.reweightK H.val) I)
            (.push (.reweightHead P hR I side Hs) k))

def Job.tag {G : Game} {B : ℕ} {A : Result G B} : Job G B A → Fin 10
  | .solve .. => 0 | .ask .. => 1 | .trials .. => 2 | .update .. => 3
  | .centers .. => 4 | .orient .. => 5 | .orientTrials .. => 6 | .orientPlus .. => 7
  | .tighten .. => 8 | .reweight .. => 9

def Frame.tag {G : Game} {B : ℕ} {A C : Result G B} : Frame G B A C → Fin 23
  | .trialsHead .. => 0 | .vectorCons .. => 1 | .median .. => 2 | .centerFirst .. => 3
  | .centerSecond .. => 4 | .centersHead .. => 5 | .orientLoop .. => 6 | .orientTail .. => 7
  | .orientHead .. => 8 | .orientCons .. => 9 | .combine .. => 10 | .tightenFirst .. => 11
  | .tightenSecond .. => 12 | .floor .. => 13 | .ceiling .. => 14 | .solveTight .. => 15
  | .solveOriented .. => 16 | .reweightHead .. => 17 | .solveReweighted .. => 18
  | .capHigh .. => 19 | .capLow .. => 20 | .includeInner .. => 21

end SourceControl
namespace Counted
@[ext] theorem ext {α : Type} {a b : Counted α} (h : a.tree = b.tree) : a = b := by
  cases a; cases b; cases h; rfl
@[simp] theorem pure_bind {α β : Type} (a : α) (f : α → Counted β) :
    (pure a).bind f = f a := by ext; simp [pure, bind, RandomTree.map]
@[simp] theorem bind_pure {α : Type} (t : Counted α) : t.bind pure = t := by
  ext; simp [bind, pure, RandomTree.map]
@[simp] theorem map_pure {α β : Type} (a : α) (f : α → β) :
    (pure a).map f = pure (f a) := rfl
@[simp] theorem map_bind {α β γ : Type} (t : Counted α) (f : α → Counted β) (g : β → γ) :
    (t.bind f).map g = t.bind (fun a => (f a).map g) := by
  ext; simp [map, bind, RandomTree.map_bind]
@[simp] theorem bind_map {α β γ : Type} (t : Counted α) (f : α → β) (g : β → Counted γ) :
    (t.map f).bind g = t.bind (fun a => g (f a)) := by
  ext; simp [map, bind]
@[simp] theorem bind_assoc {α β γ : Type} (t : Counted α) (f : α → Counted β) (g : β → Counted γ) :
    (t.bind f).bind g = t.bind (fun a => (f a).bind g) := by
  ext; simp [bind, RandomTree.map_bind, Nat.add_assoc]
@[simp] theorem map_map {α β γ : Type} (t : Counted α) (f : α → β) (g : β → γ) :
    (t.map f).map g = t.map (fun a => g (f a)) := by
  ext; simp [map]
@[simp] theorem bind_pure_eq_map {α β : Type} (t : Counted α) (f : α → β) :
    t.bind (fun a => pure (f a)) = t.map f := by
  ext; simp [bind, map, pure, RandomTree.map]
@[simp] theorem charge_bind {α β : Type} (t : Counted α) (c : ℕ) (f : α → Counted β) :
    (t.charge c).bind f = (t.bind f).charge c := by
  ext; simp [charge, bind, RandomTree.map_bind, Nat.add_assoc]
end Counted
namespace SourceControl
abbrev wholeLower {G : Game} {B : ℕ} (P : Budgets G.n) :
    CountedAlgorithm.LowerSolver (Bmax := B) P := fun Q _ I => CountedAlgorithm.solve G Q I

def Job.denote {G : Game} {B : ℕ} {A : Result G B} : Job G B A → Counted A.Value
  | .solve P I => CountedAlgorithm.solve G P I
  | .ask P I => I.repeatedCounted (CountedAlgorithm.solve G P I) (globalJ G.n B)
  | .trials P I J => Counted.trials (CountedAlgorithm.solve G P I) J
  | .update P hR I hB q => CountedAlgorithm.centerUpdate P hR (wholeLower P) I hB q
  | .centers P hR I hB t q => CountedAlgorithm.centerSteps P hR (wholeLower P) I hB t q
  | .orient P hR I => CountedAlgorithm.orient G P hR (wholeLower P) I
  | .orientTrials P hR I J => Counted.trials (CountedAlgorithm.orient G P hR (wholeLower P) I) J
  | .orientPlus P hR I => CountedAlgorithm.orientPlus
      (CountedAlgorithm.orient G P hR (wholeLower P) I) (globalJ G.n B)
  | .tighten P hR I hB => CountedAlgorithm.tighten P hR (wholeLower P) I hB
  | .reweight P _ I side Hs => Counted.traverse (fun H =>
      I.repeatedCounted (CountedAlgorithm.solve G (if side then P.reweightM H.val else P.reweightK H.val) I)
        (globalJ G.n B)) Hs

def Frame.denote {G : Game} {B : ℕ} {A C : Result G B} (f : Frame G B A C) (v : A.Value) :
    Counted C.Value := match f with
  | .trialsHead P I J => (Job.denote (.trials P I J)).map (v :: ·)
  | .vectorCons a => Counted.pure (a :: v)
  | .median I => Counted.pure (I.medianBox v)
  | .centerFirst P _ I hB q => (Job.denote (.ask P.reduceM (I.narrowCentered hB q.val))).map
      (fun r => I.averageClipped v.val r.val)
  | .centerSecond I _ _ r => Counted.pure (I.averageClipped r.val v.val)
  | .centersHead P hR I hB t q => (Job.denote (.centers P hR I hB t v)).map (q :: ·)
  | .orientLoop P hR I hB => CountedAlgorithm.orientationTail G P I v
      (fun q => CountedAlgorithm.orient G P hR (wholeLower P) (I.wideCentered hB q.val))
  | .orientTail H N => Counted.pure ⟨v.chooseY, v.exceptions ++ [H, N]⟩
  | .orientHead P hR I J => (Job.denote (.orientTrials P hR I J)).map (v :: ·)
  | .orientCons O => Counted.pure (O :: v)
  | .combine _ => Counted.pure (combineOrientations v)
  | .tightenFirst P hR I hB =>
      if _ : ∃ i, (I.delta : ℤ) ≤ v.val i - I.a i then
        (Job.denote (.tighten P hR (I.withFloor v) hB)).map fun T =>
          ⟨T.box, T.width_eq, v.property.1.trans T.floor_le, T.ceiling_le⟩
      else (Job.denote (.ask P.reduceM I)).bind fun r =>
        if _ : ∃ i, (I.delta : ℤ) ≤ I.b i - r.val i then
          (Job.denote (.tighten P hR (I.withCeiling r) hB)).map fun T =>
            ⟨T.box, T.width_eq, T.floor_le, T.ceiling_le.trans r.property.2⟩
        else Counted.pure ⟨I, rfl, le_refl _, le_refl _⟩
  | .tightenSecond P hR I hB =>
      if _ : ∃ i, (I.delta : ℤ) ≤ I.b i - v.val i then
        (Job.denote (.tighten P hR (I.withCeiling v) hB)).map fun T =>
          ⟨T.box, T.width_eq, T.floor_le, T.ceiling_le.trans v.property.2⟩
      else Counted.pure ⟨I, rfl, le_refl _, le_refl _⟩
  | .floor _ q => Counted.pure ⟨v.box, v.width_eq, q.property.1.trans v.floor_le, v.ceiling_le⟩
  | .ceiling _ q => Counted.pure ⟨v.box, v.width_eq, v.floor_le, v.ceiling_le.trans q.property.2⟩
  | .solveTight P hR _ hB =>
      have hK : 128 * globalS B < v.box.width := by rw [v.width_eq]; exact hB
      (Job.denote (.orientPlus P hR v.box)).bind fun O =>
      (CountedAlgorithm.finishChoice G P hR (wholeLower P) v.box hK O
        (CountedAlgorithm.solve G P (v.box.capHigh v.box.C v.box.C_positive (v.box.C_smaller hK).le))
        (CountedAlgorithm.solve G P (v.box.capLow v.box.C v.box.C_positive (v.box.C_smaller hK).le))).map v.include
  | .solveOriented P hR I hB => CountedAlgorithm.finishChoice G P hR (wholeLower P) I hB v
      (CountedAlgorithm.solve G P (I.capHigh I.C I.C_positive (I.C_smaller hB).le))
      (CountedAlgorithm.solve G P (I.capLow I.C I.C_positive (I.C_smaller hB).le))
  | .reweightHead P hR I side Hs => (Job.denote (.reweight P hR I side Hs)).map (v :: ·)
  | .solveReweighted P _ I hB side =>
      if side then (CountedAlgorithm.solve G P (I.capHigh I.C I.C_positive (I.C_smaller hB).le)).map
        (fun p => v.foldl I.minVector (I.includeCapHigh I.C I.C_positive (I.C_smaller hB).le p))
      else (CountedAlgorithm.solve G P (I.capLow I.C I.C_positive (I.C_smaller hB).le)).map
        (fun p => v.foldl I.maxVector (I.includeCapLow I.C I.C_positive (I.C_smaller hB).le p))
  | .capHigh I hB rs => Counted.pure (rs.foldl I.minVector (I.includeCapHigh I.C I.C_positive (I.C_smaller hB).le v))
  | .capLow I hB rs => Counted.pure (rs.foldl I.maxVector (I.includeCapLow I.C I.C_positive (I.C_smaller hB).le v))
  | .includeInner T => Counted.pure (T.include v)

def Kont.denote {G : Game} {B : ℕ} {A R : Result G B} : Kont G B A R → A.Value → Counted R.Value
  | .done, v => Counted.pure v
  | .push f k, v => (f.denote v).bind k.denote

def State.denote {G : Game} {B : ℕ} {R : Result G B} : State G B R → Counted R.Value
  | .call j k => j.denote.bind k.denote
  | .ret k v => k.denote v

theorem resume_denote {G : Game} {B : ℕ} {A C R : Result G B}
    (f : Frame G B A C) (v : A.Value) (k : Kont G B C R) :
    (resume f v k).bind State.denote = (f.denote v).bind k.denote := by
  cases f <;> simp only [resume, Frame.denote, Counted.pure_bind, Counted.bind_map,
    State.denote, Kont.denote, Counted.bind_assoc]

  case orientLoop P hR I hB =>
    unfold CountedAlgorithm.orientationTail
    try dsimp only
    split_ifs <;> simp only [Counted.pure_bind, Counted.bind_map, State.denote,
      Kont.denote, Frame.denote, Counted.bind_assoc, Job.denote]
  case tightenFirst P hR I hB =>
    split_ifs <;> simp only [Counted.pure_bind, Counted.bind_map, State.denote,
      Kont.denote, Frame.denote, Counted.bind_assoc, Job.denote]
  case tightenSecond P hR I hB =>
    split_ifs <;> simp only [Counted.pure_bind, Counted.bind_map, State.denote,
      Kont.denote, Frame.denote, Job.denote]
  case solveOriented P hR I hB =>
    unfold CountedAlgorithm.finishChoice
    try dsimp only
    cases v.chooseY <;> simp only [Bool.false_eq_true, ↓reduceIte, Job.denote, Counted.bind_assoc, wholeLower, Counted.bind_map]
  case solveReweighted P hR I hB side =>
    cases side <;> simp only [Bool.false_eq_true, ↓reduceIte, Counted.pure_bind, State.denote, Kont.denote, Frame.denote, Job.denote,
      Counted.pure_bind, Counted.bind_map]

theorem solve_notSmall {G : Game} {B : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (I : SolveBox G.n B) : CountedAlgorithm.solve G P I =
      CountedAlgorithm.solveWidth G P hR (wholeLower P) I := by
  rw [CountedAlgorithm.solve, dite_eq_right (not_lt_of_ge hR)]

theorem step_denote {G : Game} {B : ℕ} {R : Result G B} (s : State G B R) :
    (step s).bind State.denote = s.denote := by
  cases s with
  | ret k v =>
    cases k with
    | done => simp only [step, State.denote, Counted.pure_bind]
    | push f k => exact resume_denote f v k
  | call j k =>
    cases j with
    | solve P I =>
      simp only [step, State.denote, Job.denote, Counted.charge_bind]
      rw [CountedAlgorithm.solve]
      split_ifs with hR hB
      · simp only [Counted.charge_bind, Counted.pure_bind, State.denote]
      · rw [CountedAlgorithm.solveWidth]
        simp only [dite_eq_left hB, Counted.charge_bind, Counted.pure_bind, State.denote]
      · rw [CountedAlgorithm.solveWidth]
        simp only [dite_eq_right hB, Counted.charge_bind, Counted.pure_bind,
          State.denote, Job.denote, Kont.denote, Frame.denote, Counted.bind_assoc]
        congr 2
        funext T
        simp only [solve_notSmall P (le_of_not_gt hR)]
    | ask P I =>
      simp only [step, State.denote, Job.denote, Counted.pure_bind,
        Kont.denote, Frame.denote, Counted.pure_bind, SolveBox.repeatedCounted,
        Counted.bind_map]
    | trials P I J =>
      cases J <;> simp only [step, State.denote, Job.denote, Counted.pure_bind,
        Kont.denote, Frame.denote, Counted.bind_assoc, Counted.trials, Counted.bind_map]
    | update P hR I hB q =>
      simp only [step, State.denote, Job.denote, Counted.pure_bind,
        Kont.denote, Frame.denote, Counted.bind_assoc, CountedAlgorithm.centerUpdate,
        wholeLower, Counted.bind_map]
    | centers P hR I hB t q =>
      cases t <;> simp only [step, State.denote, Job.denote, Counted.pure_bind,
        Kont.denote, Frame.denote, Counted.bind_assoc, CountedAlgorithm.centerSteps,
        Counted.bind_map]
    | orient P hR I =>
      simp only [step, State.denote, Job.denote]
      rw [CountedAlgorithm.orient]
      split_ifs <;> simp only [Counted.pure_bind, State.denote, Job.denote,
        Kont.denote, Frame.denote, Counted.bind_assoc]
    | orientTrials P hR I J =>
      cases J <;> simp only [step, State.denote, Job.denote, Counted.pure_bind,
        Kont.denote, Frame.denote, Counted.bind_assoc, Counted.trials, Counted.bind_map]
    | orientPlus P hR I =>
      simp only [step, State.denote, Job.denote, Counted.pure_bind,
        Kont.denote, Frame.denote, Counted.pure_bind, CountedAlgorithm.orientPlus,
        Counted.bind_map]
    | tighten P hR I hB =>
      simp only [step, State.denote, Job.denote, Counted.pure_bind,
        Kont.denote, Frame.denote]
      rw [CountedAlgorithm.tighten, Counted.bind_assoc]
    | reweight P hR I side Hs =>
      cases Hs <;> simp only [step, State.denote, Job.denote, Counted.pure_bind,
        Kont.denote, Frame.denote, Counted.bind_assoc, Counted.traverse, Counted.bind_map]

end SourceControl

end MeanPayoff
end

end OAI
