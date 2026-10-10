import OAI.Combinatorics.PerfectMatching.Violation

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset

lemma foldl_max_le (l : List ℕ) (a b : ℕ) (ha : a≤b) (hl : ∀ x∈l,x≤b) :
    l.foldl max a≤b := by
  induction l generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    exact ih (max a x) (max_le ha (hl x (by simp))) (fun y hy => hl y (by simp [hy]))

lemma le_foldl_max (l : List ℕ) (a : ℕ) : a≤l.foldl max a := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih => exact (le_max_left a x).trans (ih (max a x))

lemma mem_le_foldl_max (l : List ℕ) (a x : ℕ) (hx : x∈l) : x≤l.foldl max a := by
  induction l generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl|h
    · exact (le_max_right a x).trans (le_foldl_max ys (max a x))
    · exact ih (max a y) h

lemma record_log_le_B (G : Input) (r : Record) (hr : r∈G.records) : Nat.log2 r.multiplicity≤B G :=
  mem_le_foldl_max _ 0 _ (List.mem_map.mpr ⟨r,hr,rfl⟩)

lemma multiplicity_log_le_B (G : Input) (e : Pair G.n) : Nat.log2 (multiplicity G e)≤B G := by
  unfold multiplicity
  cases he : G.records.find? (fun r => r.left=e.val.1.val && r.right=e.val.2.val) with
  | none => simp
  | some r => exact record_log_le_B G r (List.mem_of_find?_eq_some he)

lemma B_le_L (G : Input) : B G≤L G := by
  have h : B G≤G.n+B G+1 := by omega
  have hp : 1≤G.n+B G+1 := by omega
  have hpow : G.n+B G+1≤(G.n+B G+1)^3 := by exact Nat.le_self_pow (by omega) _
  unfold L
  omega

lemma beta_bound (G : Input) (e : Pair G.n) : |(beta G e:ℝ)|≤L G := by
  unfold beta
  split_ifs
  · simp
  · have hh := (multiplicity_log_le_B G e).trans (B_le_L G)
    norm_cast

lemma piece_slope_bound (k : ℕ) (p : Piece) (hp : p∈pieces k) : |(p.slope:ℝ)|≤k := by
  rcases (mem_pieces k p).1 hp with rfl|⟨j,hj,rfl⟩
  · simp
  · simp only [Int.cast_sub,Int.cast_natCast,Int.cast_one]
    have hj' : (j:ℝ)+1≤k := by exact_mod_cast hj
    have hj0 : (0:ℝ)≤j := by positivity
    rw [abs_le]; constructor <;> linarith

lemma piece_supergradient (k : ℕ) (p : Piece) (hp : p∈pieces k) (x : ℝ)
    (ha : p.evalReal x=psiReal k x) (z : ℝ) :
    psiReal k z≤psiReal k x+(p.slope:ℝ)*(z-x) := by
  have hh := psiReal_le_piece k z p hp
  rw [←ha]
  calc
    _ ≤ p.evalReal z := hh
    _ = p.evalReal x+(p.slope:ℝ)*(z-x) := by unfold Piece.evalReal; ring

lemma selectedPiece_supergradient (k : ℕ) (x : ℚ) (z : ℝ) :
    psiReal k z≤psiReal k (x:ℝ)+(slope k x:ℝ)*(z-(x:ℝ)) := by
  apply piece_supergradient k (selectedPiece k x)
    (List.argmin_mem (selectedPiece_mem_argmin k x)) (x:ℝ) _ z
  rw [realPsi_cast]
  simp [Piece.evalReal,Piece.eval,psi]

lemma psiReal_abs_sub (k : ℕ) (x y : ℝ) : |psiReal k x-psiReal k y|≤k*|x-y| := by
  have h (a b : ℝ) : psiReal k a-psiReal k b≤k*|a-b| := by
    have hm := List.argmin_mem (selectedReal_mem_argmin k b)
    have hh := piece_supergradient k (selectedReal k b) hm b rfl a
    have hb := piece_slope_bound k _ hm
    have hab := le_abs_self ((selectedReal k b).slope*(a-b))
    rw [abs_mul] at hab
    have hu := mul_le_mul_of_nonneg_right hb (abs_nonneg (a-b))
    linarith
  rw [abs_le]
  have hx := h x y
  have hy := h y x
  rw [abs_sub_comm y x] at hy
  exact ⟨by linarith,hx⟩

def objective (G : Input) (x : Pair G.n → ℝ) : ℝ :=
  ∑ e, (psiReal (K G.n) (x e)+(beta G e:ℝ)*x e)

def penalized (G : Input) (x : Pair G.n → ℝ) : ℝ :=
  objective G x-(M₀ G:ℝ)*violation x

lemma objective_lipschitz (G : Input) (x y : Pair G.n → ℝ) :
    |objective G x-objective G y|≤(K G.n+L G:ℝ)*∑ e,|x e-y e| := by
  unfold objective
  rw [←sum_sub_distrib,mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum; intro e _
  have he : psiReal (K G.n) (x e)+(beta G e:ℝ)*x e-
      (psiReal (K G.n) (y e)+(beta G e:ℝ)*y e)=
      (psiReal (K G.n) (x e)-psiReal (K G.n) (y e))+(beta G e:ℝ)*(x e-y e) := by ring
  rw [he]
  have hb := mul_le_mul_of_nonneg_right (beta_bound G e) (abs_nonneg (x e-y e))
  have hh := abs_add_le (psiReal (K G.n) (x e)-psiReal (K G.n) (y e)) ((beta G e:ℝ)*(x e-y e))
  rw [abs_mul] at hh
  linarith [psiReal_abs_sub (K G.n) (x e) (y e)]

lemma exact_penalty (G : Input) (hn : 4≤G.n) (heven : Even G.n)
    (x : Pair G.n → ℝ) (hx : ∀ e,x e∈Set.Icc (0:ℝ) 1) :
    ∃ y∈(completeGraph G.n).polytope,penalized G x≤objective G y := by
  obtain ⟨y,hy,hdist⟩ := violation_repair hn heven x hx
  refine ⟨y,hy,?_⟩
  have hsum : (∑ e,|x e-y e|)≤(q G.n:ℝ)*(2+10*(G.n:ℝ)^2)*violation x := by
    calc
      _ ≤ ∑ _e : Pair G.n,(2+10*(G.n:ℝ)^2)*violation x := by
        apply sum_le_sum; intro e _; rw [abs_sub_comm]; exact hdist e
      _ = _ := by simp [q,mul_assoc]
  have hh := objective_lipschitz G x y
  have hmul := mul_le_mul_of_nonneg_left hsum (show (0:ℝ)≤K G.n+L G by positivity)
  have hM : (M₀ G:ℝ)=(q G.n:ℝ)*(K G.n+L G)*(2+10*(G.n:ℝ)^2) := by
    simp [M₀,A₀]
  unfold penalized
  rw [hM]
  have hab := le_abs_self (objective G x-objective G y)
  nlinarith

lemma penalized_feasible (G : Input) (heven : Even G.n) {x : Pair G.n → ℝ}
    (hx : x∈(completeGraph G.n).polytope) : penalized G x=objective G x := by
  simp [penalized,violation_feasible heven hx]

lemma trialValue_cast (G : Input) (a : Table G.n ℤ) (r : Affine G.n) :
    (trialValue G a r:ℝ)=objective G (fun e => (coordinates (D₀ G) a e:ℝ))-
        (M₀ G:ℝ)*r.evalReal (fun e => (coordinates (D₀ G) a e:ℝ)) := by
  simp [trialValue,objective,realPsi_cast,eval_cast]

lemma trialValue_correct (G : Input) (hn : 2≤G.n) (heven : Even G.n)
    (hD : 0<D₀ G) (a : Table G.n ℤ) (ha : ∀ e,0≤entry a e) :
    (trialValue G a (activeRow (D₀ G) a):ℝ)=
      penalized G (fun e => (coordinates (D₀ G) a e:ℝ)) := by
  rw [trialValue_cast,(activeRow_correct hn heven hD a ha).2]
  rfl

lemma gradient_supergradient (G : Input) (hn : 2≤G.n) (heven : Even G.n)
    (hD : 0<D₀ G) (a : Table G.n ℤ) (ha : ∀ e,0≤entry a e)
    (z : Pair G.n → ℝ) :
    penalized G z≤penalized G (fun e => (coordinates (D₀ G) a e:ℝ))+
      ∑ e,(gradient G a (activeRow (D₀ G) a) e:ℝ)*(z e-(coordinates (D₀ G) a e:ℝ)) := by
  let x := fun e => (coordinates (D₀ G) a e:ℝ)
  let r := activeRow (D₀ G) a
  obtain ⟨hr,hract⟩ := activeRow_correct hn heven hD a ha
  have hrow := active_row_subgradient x r hr hract z
  have hf : objective G z≤objective G x+
      ∑ e,((slope (K G.n) (coordinates (D₀ G) a e):ℝ)+(beta G e:ℝ))*(z e-x e) := by
    rw [objective,objective,←sum_add_distrib]
    apply sum_le_sum; intro e _
    have hh := selectedPiece_supergradient (K G.n) (coordinates (D₀ G) a e) (z e)
    dsimp [x] at *; nlinarith
  have hm := mul_le_mul_of_nonneg_left hrow (show (0:ℝ)≤M₀ G by positivity)
  have hgrad : (∑ e,(gradient G a r e:ℝ)*(z e-x e))=
      (∑ e,((slope (K G.n) (coordinates (D₀ G) a e):ℝ)+(beta G e:ℝ))*(z e-x e))-
        (M₀ G:ℝ)*∑ e,(r.coeff e:ℝ)*(z e-x e) := by
    simp only [gradient,Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_natCast,
      sub_mul,sum_sub_distrib,mul_assoc,mul_sum]
  change penalized G z≤penalized G x+∑ e,(gradient G a r e:ℝ)*(z e-x e)
  rw [hgrad]
  unfold penalized
  linarith

lemma gradient_bound (G : Input) (hn : 2≤G.n) (heven : Even G.n)
    (hD : 0<D₀ G) (a : Table G.n ℤ) (ha : ∀ e,0≤entry a e) (e : Pair G.n) :
    |(gradient G a (activeRow (D₀ G) a) e:ℝ)|≤K G.n+L G+M₀ G := by
  have hrow := row_coeff_bound _ (activeRow_correct hn heven hD a ha).1 e
  have hs := piece_slope_bound (K G.n) _ (List.argmin_mem
    (selectedPiece_mem_argmin (K G.n) (coordinates (D₀ G) a e)))
  change |(slope (K G.n) (coordinates (D₀ G) a e):ℝ)|≤K G.n at hs
  have hm := mul_le_mul_of_nonneg_left hrow (show (0:ℝ)≤M₀ G by positivity)
  have hcast : (gradient G a (activeRow (D₀ G) a) e:ℝ)=
      (slope (K G.n) (coordinates (D₀ G) a e):ℝ)+(beta G e:ℝ)-
        (M₀ G:ℝ)*((activeRow (D₀ G) a).coeff e:ℝ) := by simp [gradient]
  rw [hcast]
  have hh := abs_sub ((slope (K G.n) (coordinates (D₀ G) a e):ℝ)+(beta G e:ℝ))
    ((M₀ G:ℝ)*((activeRow (D₀ G) a).coeff e:ℝ))
  rw [abs_mul,abs_of_nonneg (show (0:ℝ)≤M₀ G by positivity)] at hh
  linarith [abs_add_le (slope (K G.n) (coordinates (D₀ G) a e):ℝ) (beta G e:ℝ),beta_bound G e]

lemma gradient_square_bound (G : Input) (hn : 2≤G.n) (heven : Even G.n)
    (hD : 0<D₀ G) (a : Table G.n ℤ) (ha : ∀ e,0≤entry a e) :
    (∑ e,(gradient G a (activeRow (D₀ G) a) e:ℝ)^2)≤D₀ G := by
  calc
    _ ≤ ∑ _e : Pair G.n,(K G.n+L G+M₀ G:ℝ)^2 := by
      apply sum_le_sum; intro e _
      have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 (gradient_bound G hn heven hD a ha e)
      simpa only [sq_abs] using hh
    _ = D₀ G := by simp [D₀,q]

end
end BinaryMatching.Algorithm
end

end OAI
