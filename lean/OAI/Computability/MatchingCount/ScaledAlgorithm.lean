import OAI.Combinatorics.PerfectMatching.ParameterBounds

namespace OAI

section

namespace BinaryMatching.Algorithm
open Finset
local instance : Preorder ℤ := Int.instLinearOrder.toPreorder

private lemma argmin_map {α β γ : Type} [LinearOrder γ] (l : List α) (f : α → β)
    (g : β → γ) : (l.map f).argmin g=(l.argmin (g ∘ f)).map f := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    rw [List.map_append,List.map_singleton,List.argmin_concat,List.argmin_concat,ih]
    cases h : l.argmin (g ∘ f) with
    | none => rfl
    | some b => simp only [Option.map_some,Function.comp_apply]; split_ifs <;> rfl

private lemma argmin_congr_on {α β γ : Type} [LinearOrder β] [LinearOrder γ]
    (l : List α) (f : α → β) (g : α → γ)
    (h : ∀ a∈l, ∀ b∈l, f a<f b ↔ g a<g b) : l.argmin f=l.argmin g := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    have hl (b : α) (hb : b∈l) : b∈l++[a] := List.mem_append_left _ hb
    have ha : a∈l++[a] := by simp
    rw [List.argmin_concat,List.argmin_concat,ih (fun b hb c hc => h b (hl b hb) c (hl c hc))]
    cases hg : l.argmin g with
    | none => rfl
    | some b =>
      simp only
      simp only [h a ha b (hl b (List.argmin_mem hg))]

private lemma argmax_congr_on {α β γ : Type} [LinearOrder β] [LinearOrder γ]
    (l : List α) (f : α → β) (g : α → γ)
    (h : ∀ a∈l, ∀ b∈l, f a<f b ↔ g a<g b) : l.argmax f=l.argmax g :=
  @argmin_congr_on α βᵒᵈ γᵒᵈ _ _ l f g (fun a ha b hb => h b hb a ha)

def indexedPiece (k j : ℕ) : Piece :=
  if j<k then ⟨(j:ℤ)-1,(2:ℚ)⁻¹^j⟩ else ⟨k,0⟩

def pieceNumerator (k D : ℕ) (a : ℤ) (j : ℕ) : ℤ :=
  (indexedPiece k j).slope*a*2^k + if j<k then (D:ℤ)*2^(k-j) else 0

lemma pieces_indexed (k : ℕ) : pieces k=(List.range (k+1)).map (indexedPiece k) := by
  rw [List.range_succ,List.map_append,List.map_singleton]
  unfold pieces
  congr 1
  · apply List.map_congr_left
    intro j hj
    simp only [List.mem_range] at hj
    simp only [indexedPiece,ite_eq_left hj]
  · simp [indexedPiece]

lemma pieceNumerator_cast (k D j : ℕ) (hD : 0<D) (hj : j≤k) (a : ℤ) :
    (pieceNumerator k D a j:ℚ)=(D:ℚ)*2^k*(indexedPiece k j).eval (a/(D:ℚ)) := by
  have hD' : (D:ℚ)≠0 := by exact_mod_cast hD.ne'
  have hp : (2:ℚ)^k=(2:ℚ)^j*2^(k-j) := by rw [←pow_add,Nat.add_sub_of_le hj]
  unfold pieceNumerator Piece.eval indexedPiece
  split_ifs with hjk
  · push_cast
    rw [inv_pow]
    field_simp
    nlinarith [hp]
  · push_cast
    field_simp
    ring

def selectedIndex (k D : ℕ) (a : ℤ) : ℕ :=
  ((List.range (k+1)).argmin (pieceNumerator k D a)).getD k

lemma selectedIndex_mem (k D : ℕ) (a : ℤ) :
    selectedIndex k D a∈(List.range (k+1)).argmin (pieceNumerator k D a) := by
  unfold selectedIndex
  cases h : (List.range (k+1)).argmin (pieceNumerator k D a) with
  | none => have hh := List.argmin_eq_none.mp h; simp at hh
  | some j => rfl

lemma selectedIndex_le (k D : ℕ) (a : ℤ) : selectedIndex k D a≤k := by
  have h := List.argmin_mem (selectedIndex_mem k D a)
  simpa only [List.mem_range,Nat.lt_succ_iff] using h

lemma selectedPiece_index (k D : ℕ) (hD : 0<D) (a : ℤ) :
    selectedPiece k (a/(D:ℚ))=indexedPiece k (selectedIndex k D a) := by
  have hQ : (0:ℚ)<(D:ℚ)*2^k := mul_pos (by exact_mod_cast hD) (by positivity)
  have hc := argmin_congr_on (List.range (k+1))
    (fun j => (indexedPiece k j).eval (a/(D:ℚ))) (pieceNumerator k D a) (by
      intro i hi j hj
      have hi' : i≤k := by simpa only [List.mem_range,Nat.lt_succ_iff] using hi
      have hj' : j≤k := by simpa only [List.mem_range,Nat.lt_succ_iff] using hj
      rw [←mul_lt_mul_iff_right₀ hQ]
      rw [←pieceNumerator_cast k D i hD hi' a,←pieceNumerator_cast k D j hD hj' a]
      exact_mod_cast Iff.rfl)
  unfold selectedPiece selectedIndex
  rw [pieces_indexed,argmin_map]
  change (((List.range (k+1)).argmin (fun j => (indexedPiece k j).eval (a/(D:ℚ)))).map
    (indexedPiece k)).getD _=_
  rw [hc]
  cases h : (List.range (k+1)).argmin (pieceNumerator k D a) with
  | none => simp [indexedPiece]
  | some j => rfl

def scaledPsi (k D : ℕ) (a : ℤ) : ℤ := pieceNumerator k D a (selectedIndex k D a)
def scaledSlope (k D : ℕ) (a : ℤ) : ℤ := (indexedPiece k (selectedIndex k D a)).slope

lemma scaledPsi_cast (k D : ℕ) (hD : 0<D) (a : ℤ) :
    (scaledPsi k D a:ℚ)=(D:ℚ)*2^k*psi k (a/(D:ℚ)) := by
  unfold scaledPsi psi
  rw [selectedPiece_index k D hD]
  exact pieceNumerator_cast k D _ hD (selectedIndex_le k D a) a

lemma scaledSlope_eq (k D : ℕ) (hD : 0<D) (a : ℤ) :
    scaledSlope k D a=slope k (a/(D:ℚ)) := by
  unfold scaledSlope slope
  rw [selectedPiece_index k D hD]

variable {n : ℕ}

def rowNumerator (D : ℕ) (a : Table n ℤ) (r : Affine n) : ℤ :=
  (∑ e,r.coeff e*entry a e)+r.constant*D

lemma rowNumerator_cast (D : ℕ) (hD : 0<D) (a : Table n ℤ) (r : Affine n) :
    (rowNumerator D a r:ℚ)=(D:ℚ)*r.eval (coordinates D a) := by
  have hD' : (D:ℚ)≠0 := by exact_mod_cast hD.ne'
  simp only [rowNumerator,Affine.eval,coordinates,Int.cast_add,Int.cast_sum,Int.cast_mul,
    Int.cast_natCast,mul_add,mul_sum]
  congr 1
  · apply sum_congr rfl
    intro e he
    field_simp
  · ring

def integralRows (a : Table n ℤ) : List (Affine n) :=
  zeroRow :: ((List.finRange n).flatMap (fun v => [degreeRow v true,degreeRow v false])) ++
    [cutRow (DenseOracle.oddCut (DenseOracle.make (capacities a)) univ)]

lemma integralRows_eq (a : Table n ℤ) : integralRows a=activeRows a := by
  simp only [integralRows,DenseOracle.oddCut_eq,DenseOracle.view_make,activeRows]

def integralRow (D : ℕ) (a : Table n ℤ) : Affine n :=
  ((integralRows a).argmax (rowNumerator D a)).getD zeroRow

lemma integralRow_eq (D : ℕ) (hD : 0<D) (a : Table n ℤ) :
    integralRow D a=activeRow D a := by
  unfold integralRow activeRow
  rw [integralRows_eq]
  congr 1
  apply argmax_congr_on
  intro r hr s hs
  rw [←Int.cast_lt (R := ℚ),rowNumerator_cast D hD,rowNumerator_cast D hD]
  exact mul_lt_mul_iff_right₀ (by exact_mod_cast hD)

def integralValue (G : Input) (a : Table G.n ℤ) (r : Affine G.n) : ℤ :=
  (∑ e, (scaledPsi (K G.n) (D₀ G) (entry a e)+beta G e*entry a e*2^(K G.n))) -
    (M₀ G:ℤ)*rowNumerator (D₀ G) a r*2^(K G.n)

def integralGradient (G : Input) (a : Table G.n ℤ) (r : Affine G.n) (e : Pair G.n) : ℤ :=
  scaledSlope (K G.n) (D₀ G) (entry a e)+beta G e-(M₀ G:ℤ)*r.coeff e

def integralUpdate (G : Input) (a : Table G.n ℤ) (r : Affine G.n) : Table G.n ℤ :=
  toTable (fun e => min (D₀ G:ℤ) (max 0 (entry a e+integralGradient G a r e)))

lemma integralGradient_eq (G : Input) (hn : 2≤G.n) (a : Table G.n ℤ) (r : Affine G.n) :
    integralGradient G a r=gradient G a r := by
  funext e
  simp only [integralGradient,gradient,coordinates,scaledSlope_eq _ _ (D₀_pos G hn)]

lemma integralUpdate_eq (G : Input) (hn : 2≤G.n) (a : Table G.n ℤ) (r : Affine G.n) :
    integralUpdate G a r=update G a r := by
  simp only [integralUpdate,update,integralGradient_eq G hn]

lemma integralValue_cast (G : Input) (hn : 2≤G.n) (a : Table G.n ℤ) (r : Affine G.n) :
    (integralValue G a r:ℚ)=(Q G:ℚ)*trialValue G a r := by
  have hD : (D₀ G:ℚ)≠0 := by exact_mod_cast (D₀_pos G hn).ne'
  simp only [integralValue,Int.cast_sub,Int.cast_sum,Int.cast_add,Int.cast_mul,Int.cast_pow,
    Int.cast_ofNat,Int.cast_natCast,scaledPsi_cast _ _ (D₀_pos G hn),
    rowNumerator_cast _ (D₀_pos G hn),trialValue,Q,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
    mul_sub,mul_sum,mul_add,coordinates]
  congr 1
  · apply sum_congr rfl
    intro e he
    field_simp
  · ring

structure IntegralState (n : ℕ) where
  numerators : Table n ℤ
  best : Option ℤ

def integralStep (G : Input) (s : IntegralState G.n) : IntegralState G.n :=
  let r := integralRow (D₀ G) s.numerators
  let value := integralValue G s.numerators r
  ⟨integralUpdate G s.numerators r,some (s.best.elim value (max value))⟩

def integralInitial (n : ℕ) : IntegralState n := ⟨tabulate (fun _ _ => 0),none⟩

def integralIterate (G : Input) : ℕ → IntegralState G.n
  | 0 => integralInitial G.n
  | t+1 => integralStep G (integralIterate G t)

end BinaryMatching.Algorithm
end

end OAI
