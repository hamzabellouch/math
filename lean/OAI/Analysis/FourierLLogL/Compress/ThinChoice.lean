import OAI.Analysis.FourierLLogL.Compress.Select
/-! # Thinning to exact row marginals -/
open Set Function Filter
open scoped BigOperators
noncomputable section
namespace OAI

namespace FourierLLogL.Compress
open Law Real
variable {A B Ω ι κ : Type} [Fintype A] [Fintype B] [DecidableEq B] [Fintype Ω] {n r : ℕ}

abbrev Ticket (r n : ℕ) := Option (Fin r ↪ Fin n)


def gain (j : Fin r) (f : Fin n → ℝ) : Ticket r n → ℝ
  | none => 0
  | some e => f (e j)

private lemma perm_uniform (x : B) :
    (uniform (Equiv.Perm B)).send (fun e => e x) = letI : Nonempty B := ⟨x⟩; uniform B := by
  have : Nonempty B := ⟨x⟩
  let R := uniform (Equiv.Perm B)
  let W := R.send (fun e => e x)
  have he (a b : B) : W a = W b := by
    classical
    let f := Equiv.swap a b
    have hh (e : Equiv.Perm B) : (e x=a) ↔ (f*e) x=b := by
      change _ ↔ f (e x) = _
      rw [← show f a = b from Equiv.swap_apply_left _ _, f.injective.eq_iff]
    unfold W; rw [send_apply,send_apply,prob_eq,prob_eq]
    exact Fintype.sum_equiv (Equiv.mulLeft f) _ _ fun i => by
      change _ = if (f*i) x=b then _ else _
      split_ifs <;> simp_all only
      all_goals first | rfl | exact False.elim (by grind)
  apply Law.ext
  intro a
  have hh (w : B) := he w a
  have H := W.total
  simp_rw [hh, Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at H
  change W a = _
  rw [uniform_apply]
  field_simp
  linarith

private lemma count_frac (s : Finset (Fin n)) (hn : 0 < n) :
    0 ≤ (s.card:ℝ)/n ∧ (s.card:ℝ)/n ≤ 1 := by
  have hp : (0:ℝ)< n := by exact_mod_cast hn
  constructor
  · positivity
  · apply (div_le_one hp).mpr
    exact_mod_cast (by simpa using Finset.card_le_univ s : s.card ≤ n)

/-- Sampling rule for the realized set of tagged input blocks. -/
lemma choose_tickets (r n : ℕ) (hr : 0 < r) (hn : 0 < n) (s : Finset (Fin n)) :
    ∃ k : Law (Ticket r n), ∀ (j : Fin r) (f : Fin n → ℝ),
      k.Ex (gain j f) = if r ≤ s.card then (∑ i ∈ s, f i)/n else 0 := by
  classical
  by_cases hs : r ≤ s.card
  · have he : r ≤ Fintype.card s := by simpa using hs
    have : Nonempty s := Fintype.card_pos_iff.mp (lt_of_lt_of_le hr he)
    let t := (s.card:ℝ)/n
    let g : Fin r ↪ s := (Fin.castLEEmb he).trans (Fintype.equivFin _).symm.toEmbedding
    let T (f : Equiv.Perm s) : Ticket r n :=
      some ((g.trans f.toEmbedding).trans (Embedding.subtype _))
    refine ⟨mixture ((uniform (Equiv.Perm s)).send T) (point none) t
      (count_frac _ hn).1 (count_frac _ hn).2,?_⟩
    intro j f
    rw [ite_eq_left hs, mixture_Ex,Ex_point,Ex_send]
    dsimp only [gain,T]
    let F (x : s) := f x

    change t*(uniform (Equiv.Perm s)).Ex (fun i => F (i (g j))) + _*0 = _
    have h : (uniform (Equiv.Perm s)).Ex (fun i => F (i (g j))) = (uniform s).Ex F := by
      have H := Ex_send (uniform (Equiv.Perm s)) (fun i => i (g j)) F
      rw [perm_uniform] at H
      exact H.symm
    rw [h]
    unfold t Ex F
    have hh : 0 < (s.card:ℝ) := by exact_mod_cast lt_of_lt_of_le hr hs
    simp only [uniform_apply,← Finset.mul_sum,mul_zero,add_zero, Fintype.card_coe,
      Finset.univ_eq_attach,Finset.sum_attach]
    field_simp
  · refine ⟨point none,fun j f => ?_⟩
    rw [ite_eq_right hs,Ex_point]; rfl

/-- A numerical tag probability. -/
private def ratio (a b : ℝ) := min a b/a

private lemma ratio_bounds (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ ratio a b ∧ ratio a b ≤ 1 ∧ a * ratio a b = min a b := by
  unfold ratio
  obtain hx|hx := eq_or_lt_of_le ha
  · simp [← hx,hb]
  exact ⟨div_nonneg (le_min ha hb) ha, (div_le_one hx).mpr (min_le_left _ _), by field_simp⟩

def tagChance (p q : Law A) (x : A) : Law Bool :=
  coinP (ratio (p x) (q x)) (ratio_bounds _ _ (p.nonneg _) (q.nonneg _)).1
    (ratio_bounds _ _ (p.nonneg _) (q.nonneg _)).2.1

lemma tag_test (p q : Law A) (f : A → ℝ) :
    p.Ex (fun x => (tagChance p q x).Ex (fun b : Bool => if b then f x else 0)) =
      ∑ x, min (p x) (q x) * f x := by
  unfold tagChance
  simp_rw [coinP_Ex]
  simp only [Bool.false_eq_true, ↓reduceIte,mul_zero,add_zero,Ex,← mul_assoc,
    (ratio_bounds (p _) (q _) (p.nonneg _) (q.nonneg _)).2.2]

/-- Build a channel from the underlying input to the rejection/selected rows. -/
lemma thin_sampler (r n : ℕ) (hr : 0 < r) (hn : n=2*r) (P : Law Ω) (q : Law A)
    (X : Ω → Fin n → A) (ε : ℝ)
    (hε : ∀ i, ((P.send fun x => X x i).tv q) ≤ ε) :
    ∃ (k : Ω → Law (Ticket r n)),
      let R := P.withNext k
      R.prob (fun x => x.2 = none) ≤ 2 * ε ∧
      (∀ (j : Fin r) (f : A → ℝ) (_h : ∀ x, 0 ≤ f x),
        R.Ex (fun x => gain j (fun i => f (X x.1 i)) x.2) ≤ q.Ex f) := by
  classical
  have hnp : 0 < n := by omega
  have hNr : (0:ℝ) < n := by exact_mod_cast hnp
  choose c hc using choose_tickets r n hr hnp
  let p (i : Fin n) := P.send fun x => X x i
  let Q (x) := pack (fun i : Fin n => tagChance (p i) q (X x i))
  let S (x : Fin n → Bool) := Finset.univ.filter (fun i => x i = true)
  let k (x : Ω) := (Q x).through fun y => c (S y)
  let R := P.withNext k
  have hTag (x) (f : Fin n → ℝ) :
      (Q x).Ex (fun b => ∑ i ∈ S b, f i) =
        ∑ i : Fin n, (tagChance (p i) q (X x i)).Ex (fun b : Bool => if b then f i else 0) := by
    unfold S Q
    simp_rw [Finset.sum_filter,Ex_finset_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact Ex_pack_proj _ i (fun b : Bool => if b then f i else 0)
  have hComp (f : A → ℝ) :
      P.Ex (fun x => (Q x).Ex fun b => ∑ i ∈ S b, f (X x i)) =
        ∑ i : Fin n, ∑ a, min (p i a) (q a) * f a := by
    have HH (x : Ω) := hTag x (fun i => f (X x i))
    simp_rw [HH,Ex_finset_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [← tag_test]
    exact (Ex_send P (fun x => X x i) (fun y =>
      (tagChance (p i) q y).Ex (fun b => if b then f y else 0))).symm
  have hTick (x) (j : Fin r) (f : Fin n → ℝ) :
      (k x).Ex (gain j f) =
        (Q x).Ex (fun b => if r ≤ (S b).card then (∑ i ∈ S b, f i)/n else 0) := by
    unfold k; rw [Ex_through]; simp_rw [hc]
  refine ⟨k,?_,?_⟩
  · let j : Fin r := ⟨0,hr⟩
    let F := fun (_ : Fin n) => (1:ℝ)
    have hg : R.prob (fun x => x.2 = none) =
        1 - P.Ex (fun x => (k x).Ex (gain j F)) := by
      unfold prob
      rw [← Ex_withNext P k (fun x => gain j F x.2)]
      calc
        _ = R.Ex fun x => 1-gain j F x.2 := by
          congr 1; funext x; cases x with
          | mk a b => cases b <;> simp [gain,F]
        _ = _ := by rw [Ex_sub (f:=fun _ => 1),Ex_const]
    have h1 (x : Ω) :
        2/n * (Q x).Ex (fun b => ∑ i ∈ S b, F i)-1 ≤ (k x).Ex (gain j F) := by
      rw [hTick]
      have HH (b : Fin n → Bool) :
          2/(n:ℝ) * (∑ i ∈ S b, F i) - 1 ≤ if r ≤ (S b).card then
            (∑ i ∈ S b, F i)/n else 0 := by
        have ha : (↑n:ℝ) = 2*(r:ℝ) := by exact_mod_cast hn
        have hb : ((S b).card:ℝ) ≤ n := by exact_mod_cast
          (by simpa using Finset.card_le_univ (S b) : (S b).card ≤ n)
        simp only [F,Finset.sum_const,nsmul_eq_mul,mul_one]
        split_ifs with H
        · field_simp; linarith
        · have : ((S b).card:ℝ) ≤ r := by exact_mod_cast (le_of_not_ge H)
          field_simp; linarith
      refine le_trans (b:=(Q x).Ex (fun b => 2/(n:ℝ)*(∑ i ∈ S b, F i)-1))
        ?_ (Ex_mono _ HH)
      rw [Ex_sub,Ex_lmul,Ex_const]
    have HE := hComp (fun _ => 1)
    have HF : (n:ℝ)*(1-ε) ≤ P.Ex fun x => (Q x).Ex (fun b => ∑ i ∈ S b, F i) := by
      unfold F; rw [HE]
      simp_rw [mul_one,tv_common]
      apply le_trans (b:=∑ i : Fin n,(1-ε)) _ (Finset.sum_le_sum _)
      · simp; apply le_of_eq; ring
      intro i _; exact sub_le_sub_left (hε i) _
    have HL := P.Ex_mono h1
    rw [Ex_sub,Ex_lmul,Ex_const] at HL
    change R.prob _ ≤ _
    rw [hg]
    field_simp at HL

    nlinarith
  · intro j f hf
    change R.Ex _ ≤ _
    unfold R; rw [Ex_withNext]
    have h1 (x : Ω) :
        (k x).Ex (gain j (fun i => f (X x i))) ≤
          (Q x).Ex (fun b => ∑ i ∈ S b, f (X x i)) * (n:ℝ)⁻¹ := by
      rw [hTick, ← Ex_mul]
      apply Ex_mono
      intro b
      split_ifs
      · simp [div_eq_mul_inv]
      · exact mul_nonneg (Finset.sum_nonneg (fun i _ => hf _)) (by positivity)
    refine le_trans (Ex_mono P h1) ?_
    rw [Ex_mul,hComp]
    apply le_trans (b := (∑ i : Fin n, q.Ex f) * (n:ℝ)⁻¹)
    · apply mul_le_mul_of_nonneg_right _ (by positivity)
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_right (min_le_right _ _) (hf _)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    apply le_of_eq; field_simp

end FourierLLogL.Compress

end OAI
