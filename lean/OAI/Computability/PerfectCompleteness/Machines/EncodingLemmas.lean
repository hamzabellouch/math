import Mathlib.Tactic.Ring
import OAI.Computability.PerfectCompleteness.Model
import OAI.Computability.PerfectCompleteness.Reduction.Target
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas

namespace OAI


namespace PerfectCompleteness.Encoding

open UniqueGamesTheorem.Foundations.Complexity

def parseLabel (alphabet value : Nat) : Option (Fin alphabet) :=
  if bounded : value < alphabet then some ⟨value, bounded⟩ else none

@[simp] theorem parseLabel_value {q : Nat} (label : Fin q) :
    parseLabel q label.val = some label := by
  simp [parseLabel, label.isLt]

@[simp] theorem parseLabels_values {q : Nat} (labels : List (Fin q)) :
    (labels.map Fin.val).mapM (parseLabel q) = some labels := by
  induction labels with
  | nil => rfl
  | cons label labels ih => simp [ih]

def parseImages (alphabet : Nat) (words : List Nat) :
    Option (Vector (Fin alphabet) (2 * alphabet)) := do
  let labels ← words.mapM (parseLabel alphabet)
  if length_ok : labels.length = 2 * alphabet then
    some ⟨labels.toArray, by simpa using length_ok⟩
  else none

@[simp] theorem parseImages_values {q : Nat}
    (images : Vector (Fin q) (2 * q)) :
    parseImages q (images.toList.map Fin.val) = some images := by
  unfold parseImages
  rw [parseLabels_values]
  simp
  exact Vector.toArray_toList

def parseProjection (alphabet : Nat) (words : List Nat) :
    Option (ProjectionTable alphabet) := do
  let images ← parseImages alphabet words
  if exactlyTwo : ∀ b : Fin alphabet,
      ((List.finRange (2 * alphabet)).filter
        (fun a => decide (images[a] = b))).length = 2 then
    some ⟨images, exactlyTwo⟩
  else none

@[simp] theorem parseProjection_encoded {q : Nat} (table : ProjectionTable q) :
    parseProjection q (tableWords table) = some table := by
  simp only [parseProjection, tableWords, parseImages_values]
  dsimp only [Bind.bind, Option.bind]
  simp only [table.exactlyTwo, implies_true, dite_true]

@[simp] theorem tableWords_length {q : Nat} (table : ProjectionTable q) :
    (tableWords table).length = 2 * q := by
  simp [tableWords]

def parseEdge (leftVertices rightVertices alphabet : Nat) :
    List Nat → Option (Edge leftVertices rightVertices alphabet × List Nat)
  | left :: right :: words => do
      let left ← parseLabel leftVertices left
      let right ← parseLabel rightVertices right
      let projection ← parseProjection alphabet (words.take (2 * alphabet))
      return (⟨left, right, projection⟩, words.drop (2 * alphabet))
  | _ => none

@[simp] theorem parseEdge_encoded {l r q : Nat}
    (edge : Edge l r q) (rest : List Nat) :
    parseEdge l r q (edgeWords edge ++ rest) = some (edge, rest) := by
  cases edge with
  | mk left right projection =>
      have taken := List.take_left' (l₂ := rest) (tableWords_length projection)
      have dropped := List.drop_left' (l₂ := rest) (tableWords_length projection)
      simp [edgeWords, parseEdge, taken, dropped]

def parseEdges (leftVertices rightVertices alphabet : Nat) :
    Nat → List Nat → Option (List (Edge leftVertices rightVertices alphabet) × List Nat)
  | 0, words => some ([], words)
  | count + 1, words => do
      let (edge, words) ← parseEdge leftVertices rightVertices alphabet words
      let (edges, words) ← parseEdges leftVertices rightVertices alphabet count words
      return (edge :: edges, words)

@[simp] theorem parseEdges_encoded {l r q : Nat}
    (edges : List (Edge l r q)) (rest : List Nat) :
    parseEdges l r q edges.length (edges.flatMap edgeWords ++ rest) =
      some (edges, rest) := by
  induction edges with
  | nil => rfl
  | cons edge edges ih => simp [parseEdges, List.append_assoc, ih]

def decodeGameWords (alphabet : Nat) : List Nat → Option (Instance alphabet)
  | leftVertices :: rightVertices :: encodedAlphabet :: count :: words => do
      if encodedAlphabet = alphabet then
        let (edges, trailing) ← parseEdges leftVertices rightVertices alphabet count words
        if trailing = [] then
          if nonempty : edges ≠ [] then
            some ⟨leftVertices, rightVertices, edges, nonempty⟩
          else none
        else none
      else none
  | _ => none

@[simp] theorem decodeGameWords_encoded {q : Nat} (game : Instance q) :
    decodeGameWords q (gameWords game) = some game := by
  cases game with
  | mk leftVertices rightVertices edges nonempty =>
      have parsed := parseEdges_encoded edges []
      simp only [List.append_nil] at parsed
      simp [decodeGameWords, gameWords, parsed, nonempty]

def decodeGameBits (alphabet : Nat) (bits : List Bool) : Option (Instance alphabet) :=
  decodeWords bits >>= decodeGameWords alphabet

@[simp] theorem decodeGameBits_encoded {q : Nat} (game : Instance q) :
    decodeGameBits q (gameBits game) = some game := by
  simp [decodeGameBits, gameBits]

theorem gameBits_injective {q : Nat} {first second : Instance q}
    (same : gameBits first = gameBits second) : first = second := by
  have parsed := congrArg (decodeGameBits q) same
  simpa only [decodeGameBits_encoded, Option.some.injEq] using parsed

@[simp] theorem edgeWords_length {l r q : Nat} (edge : Edge l r q) :
    (edgeWords edge).length = 2 * q + 2 := by
  simp [edgeWords]

theorem edgesWords_length {l r q : Nat} (edges : List (Edge l r q)) :
    (edges.flatMap edgeWords).length = edges.length * (2 * q + 2) := by
  induction edges with
  | nil => simp
  | cons edge edges ih =>
      simp only [List.flatMap_cons, List.length_append, edgeWords_length,
        List.length_cons, Nat.add_mul, Nat.one_mul, ih]
      omega

@[simp] theorem gameWords_length {q : Nat} (game : Instance q) :
    (gameWords game).length = 4 + game.edges.length * (2 * q + 2) := by
  simp only [gameWords, List.length_append, List.length_cons, List.length_nil,
    edgesWords_length]

theorem gameBits_length {q : Nat} (game : Instance q) :
    (gameBits game).length =
      (gameWords game).sum + 4 + game.edges.length * (2 * q + 2) := by
  simp only [gameBits, encodeWords_length, gameWords_length]
  omega

end PerfectCompleteness.Encoding


namespace PerfectCompleteness.Encoding

theorem tableWords_sum_le {q : Nat} (table : ProjectionTable q) :
    (tableWords table).sum ≤ 2 * q * q := by
  have hsum (labels : List (Fin q)) :
      (labels.map Fin.val).sum ≤ labels.length * q := by
    induction labels with
    | nil => simp
    | cons a labels ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons,
          Nat.add_mul, Nat.one_mul]
        calc
          _ ≤ q + labels.length * q :=
            Nat.add_le_add (Nat.le_of_lt a.isLt) ih
          _ = labels.length * q + q := Nat.add_comm _ _
  simpa [tableWords] using hsum table.images.toList

theorem edgeWords_sum_le {l r q : Nat} (edge : Edge l r q) :
    (edgeWords edge).sum ≤ l + r + 2 * q * q := by
  calc
    _ = edge.left.val + edge.right.val + (tableWords edge.projection).sum := by
      simp [edgeWords, Nat.add_assoc]
    _ ≤ l + r + 2 * q * q :=
      Nat.add_le_add
        (Nat.add_le_add (Nat.le_of_lt edge.left.isLt) (Nat.le_of_lt edge.right.isLt))
        (tableWords_sum_le edge.projection)

theorem edgesWords_sum_le {l r q : Nat} (edges : List (Edge l r q)) :
    (edges.flatMap edgeWords).sum ≤ edges.length * (l + r + 2 * q * q) := by
  induction edges with
  | nil => simp
  | cons edge edges ih =>
      calc
        _ = (edgeWords edge).sum + (edges.flatMap edgeWords).sum := by
          rw [List.flatMap_cons, List.sum_append]
        _ ≤ (l + r + 2 * q * q) + edges.length * (l + r + 2 * q * q) :=
          Nat.add_le_add (edgeWords_sum_le edge) ih
        _ = (edge :: edges).length * (l + r + 2 * q * q) := by
          simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
          exact Nat.add_comm _ _

theorem gameWords_sum_le {q : Nat} (game : Instance q) :
    (gameWords game).sum ≤
      game.leftVertices + game.rightVertices + q + game.edges.length +
        game.edges.length * (game.leftVertices + game.rightVertices + 2 * q * q) := by
  calc
    _ = (game.leftVertices + game.rightVertices + q + game.edges.length) +
        (game.edges.flatMap edgeWords).sum := by
      simp [gameWords, Nat.add_assoc]
    _ ≤ _ := Nat.add_le_add_left (edgesWords_sum_le game.edges) _

theorem gameBits_length_le {q : Nat} (game : Instance q) :
    (gameBits game).length ≤
      game.leftVertices + game.rightVertices + q + game.edges.length + 4 +
        game.edges.length *
          (game.leftVertices + game.rightVertices + 2 * q * q + 2 * q + 2) := by
  rw [gameBits_length]
  calc
    _ ≤ (game.leftVertices + game.rightVertices + q + game.edges.length +
        game.edges.length * (game.leftVertices + game.rightVertices + 2 * q * q)) +
          4 + game.edges.length * (2 * q + 2) :=
      Nat.add_le_add_right (Nat.add_le_add_right (gameWords_sum_le game) 4) _
    _ = _ := by ring

theorem gameBits_length_le_of_edge_count {q : Nat} (game : Instance q)
    (M : Nat) (hM : game.edges.length ≤ M) :
    (gameBits game).length ≤
      game.leftVertices + game.rightVertices + q + M + 4 +
        M * (game.leftVertices + game.rightVertices + 2 * q * q + 2 * q + 2) := by
  apply (gameBits_length_le game).trans
  exact Nat.add_le_add
    (Nat.add_le_add_right
      (Nat.add_le_add_left hM (game.leftVertices + game.rightVertices + q)) 4)
    (Nat.mul_le_mul_right
      (game.leftVertices + game.rightVertices + 2 * q * q + 2 * q + 2) hM)

end PerfectCompleteness.Encoding

end OAI
