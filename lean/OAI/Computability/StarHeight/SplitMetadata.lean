import OAI.Computability.StarHeight.CanonicalEpisodes

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uM uS uK uM2 uM3 uS2 uM4 uS3
universe uM5 uS4 uM6 uS5 uK2 uM7 uS6 uK3

namespace SplitMetadata

variable {M : Type uM} {S : Type uS} {K : Type uK} [Field K] [AddCommGroup S] [Module K S]

abbrev Omitted (M : Type uM2) (g : ℕ) (j : Fin g) := {i : Fin g // i ≠ j} → M

def insert {g : ℕ} (j : Fin g) (d : Omitted M g j) (a : M) : Fin g → M :=
  fun i => if h : i = j then a else d ⟨i,h⟩

@[simp] lemma insert_at {g : ℕ} (j : Fin g) (d : Omitted M g j) (a : M) :
    insert j d a j = a := by simp [insert]

lemma insert_away {g : ℕ} (j i : Fin g) (d : Omitted M g j) (a : M) (h : i ≠ j) :
    insert j d a i = d ⟨i,h⟩ := by simp [insert,h]

lemma insert_actual {g : ℕ} (j : Fin g) (d : Fin g → M) :
    insert j (fun i => d i) (d j) = d := by
  funext i
  by_cases h : i = j <;> simp [insert,h]

lemma insert_eq_update {g : ℕ} (j : Fin g) (d : Fin g → M) (a : M) :
    insert j (fun i => d i) a = Function.update d j a := by
  funext i
  by_cases h : i = j <;> simp [insert,h]

structure MainTag (M : Type uM3) (S : Type uS2) (g B : ℕ) where
  j : Fin g
  u : Fin B
  A : M
  C : M
  entries : Omitted M g j
  input : S
  output : S

noncomputable instance [Fintype M] [Fintype S] {g B : ℕ} : Fintype (MainTag M S g B) := by
  classical
  apply Fintype.ofInjective (fun t : MainTag M S g B =>
    (⟨t.j, (t.u,t.A,t.C,t.entries,t.input,t.output)⟩ :
      Σ j : Fin g, Fin B × M × M × Omitted M g j × S × S))
  intro a b he
  cases a with | mk aj au aa ac ad ax ay =>
    cases b with | mk bj bu ba bc bd bx byy =>
      have hj : aj = bj := congrArg Sigma.fst he
      subst bj
      have hh : (au,aa,ac,ad,ax,ay) = (bu,ba,bc,bd,bx,byy) :=
        eq_of_heq (Sigma.mk.inj_iff.mp he).2
      simp only [Prod.mk.injEq] at hh
      rcases hh with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
      rfl

structure PeriodicTag (M : Type uM4) (S : Type uS3) (g B : ℕ) where
  j : Fin (g + 1)
  u : Fin B
  prefixProduct : M
  input : S
  output : S
  deriving Fintype

abbrev Tag (M : Type uM5) (S : Type uS4) (g B : ℕ) := MainTag M S g B ⊕ PeriodicTag M S g B

def Tag.input {g B : ℕ} : Tag M S g B → S
  | .inl a => a.input
  | .inr a => a.input

def Tag.output {g B : ℕ} : Tag M S g B → S
  | .inl a => a.output
  | .inr a => a.output

def Tag.residue {g B : ℕ} : Tag M S g B → Fin B
  | .inl a => a.u
  | .inr a => a.u

structure Kind (M : Type uM6) (S : Type uS5) (K : Type uK2) [CommSemiring K] [AddCommMonoid S] [Module K S] (g : ℕ) where
  j : Fin g
  input : S
  output : S
  entries : Omitted M g j
  hypothetical : M → (S →ₗ[K] S)

noncomputable instance [Fintype M] [Fintype S] {g : ℕ} : Fintype (Kind M S K g) := by
  classical
  apply Fintype.ofInjective (fun t : Kind M S K g =>
    (⟨t.j, (t.input,t.output,t.entries, fun a x => t.hypothetical a x)⟩ :
      Σ j : Fin g, S × S × Omitted M g j × (M → S → S)))
  intro a b he
  cases a with | mk aj ax ay ad af =>
    cases b with | mk bj bx byy bd bf =>
      have hj : aj = bj := congrArg Sigma.fst he
      subst bj
      have hh : (ax,ay,ad,fun a x => af a x) = (bx,byy,bd,fun a x => bf a x) :=
        eq_of_heq (Sigma.mk.inj_iff.mp he).2
      have hp := Prod.mk.inj hh
      have hp' := Prod.mk.inj hp.2
      have hp'' := Prod.mk.inj hp'.2
      have hf : af = bf := by
        funext a
        ext x
        exact congrFun (congrFun hp''.2 a) x
      cases hp.1; cases hp'.1; cases hp''.1; cases hf
      rfl

abbrev Roster (M : Type uM7) (S : Type uS6) (K : Type uK3) [CommSemiring K] [AddCommMonoid S] [Module K S]
    (g μ : ℕ) := Kind M S K g × Fin μ

lemma certificate_at_actual {g : ℕ} (f : (Fin g → M) → (S →ₗ[K] S))
    (β : (Fin g → M) → S) (d : Fin g → M) (j : Fin g) (x y : S)
    (h : ∀ a, f (insert j (fun i => d i) a) x + β (insert j (fun i => d i) a) = y) :
    f d x + β d = y := by
  simpa only [insert_actual] using h (d j)

lemma certificate_available {g : ℕ} (f : (Fin g → M) → (S →ₗ[K] S))
    (β : (Fin g → M) → S) (hβ : ShiftTableProperty g f β)
    (d : Fin g → M) (x : S) :
    ∃ j : Fin g, ∀ a, f (insert j (fun i => d i) a) x +
      β (insert j (fun i => d i) a) = f d x + β d := by
  obtain ⟨j,hj⟩ := hβ d x
  exact ⟨j, fun a => by simpa only [insert_eq_update] using hj a⟩

end SplitMetadata

namespace IntegerSchedules

lemma multiple_gt (B : ℤ) (hB : 0 < B) (L : ℤ) :
    ∃ x : ℤ, 0 < x ∧ B ∣ x ∧ L < x := by
  refine ⟨B * (|L| + 1), mul_pos hB (by positivity), dvd_mul_right B _, ?_⟩
  have hBn : 1 ≤ B := hB
  have habs := le_abs_self L
  have ha := abs_nonneg L
  nlinarith

structure Inner (B n R size d K : ℕ) (r h : ℤ) where
  lag : ℤ
  extension : ℤ
  H : Fin B → ℤ
  Hmax : ℤ
  halfGap : ℤ
  lag_pos : 0 < lag
  lag_multiple : (B : ℤ) ∣ lag
  lag_bound : r + (size + 2 : ℕ) * (d : ℤ) < lag
  extension_bound : lag + (n * d * size.factorial * B : ℕ) + 2 * d < extension
  H_pos : ∀ u, 0 < H u
  H_multiple : ∀ u, (B : ℤ) ∣ H u
  H_large : ∀ u, 2 * (d : ℤ) < H u
  H_bounded : ∀ u, H u ≤ Hmax
  H_separated : ∀ u v, u ≠ v →
    2 * h + 2 * max extension (B * R : ℕ) + 2 < |H u - H v|
  gap_pos : 0 < halfGap
  gap_multiple : (B : ℤ) ∣ halfGap
  gap_bound : 10 * (Hmax + extension + r + K + d + (B * R : ℕ) + 1) < 2 * halfGap

lemma exists_inner (B n R size d K : ℕ) (r h : ℤ) (hB : 0 < B) :
    Nonempty (Inner B n R size d K r h) := by
  have hBi : (0 : ℤ) < B := by exact_mod_cast hB
  obtain ⟨lag,hlag,hlagB,hlagbound⟩ := multiple_gt B hBi (r + (size + 2 : ℕ) * (d : ℤ))
  let extension : ℤ := lag + (n * d * size.factorial * B : ℕ) + 2 * d + 1
  obtain ⟨base,hbase,hbaseB,hbasebound⟩ := multiple_gt B hBi (2 * d)
  obtain ⟨step,hstep,hstepB,hstepbound⟩ := multiple_gt B hBi
    (2 * h + 2 * max extension (B * R : ℕ) + 2)
  let H (u : Fin B) : ℤ := base + u.val * step
  let Hmax : ℤ := base + (B - 1 : ℕ) * step
  obtain ⟨gap,hgap,hgapB,hgapbound⟩ := multiple_gt B hBi
    (10 * (Hmax + extension + r + K + d + (B * R : ℕ) + 1))
  refine ⟨⟨lag,extension,H,Hmax,gap,hlag,hlagB,hlagbound,?_,?_,?_,?_,?_,?_,
    hgap,hgapB,by omega⟩⟩
  · dsimp [extension]; omega
  · intro u; dsimp [H]; positivity
  · intro u
    exact dvd_add hbaseB (dvd_mul_of_dvd_right hstepB _)
  · intro u
    dsimp [H]
    have hh : 0 ≤ (u.val : ℤ) * step := mul_nonneg (by positivity) hstep.le
    omega
  · intro u
    dsimp [H,Hmax]
    have hu : (u.val : ℤ) ≤ (B - 1 : ℕ) := by exact_mod_cast Nat.le_pred_of_lt u.isLt
    exact add_le_add_right (mul_le_mul_of_nonneg_right hu hstep.le) _
  · intro u v huv
    have hne : (u.val : ℤ) ≠ v.val := by
      intro he
      apply huv
      exact Fin.ext (by exact_mod_cast he)
    have hd : 1 ≤ |(u.val : ℤ) - v.val| := by
      have hp : 0 < |(u.val : ℤ) - v.val| := abs_pos.mpr (sub_ne_zero.mpr hne)
      omega
    have he : H u - H v = ((u.val : ℤ) - v.val) * step := by dsimp [H]; ring
    rw [he,abs_mul,abs_of_pos hstep]
    exact hstepbound.trans_le (le_mul_of_one_le_left hstep.le hd)

end IntegerSchedules

namespace IntegerSchedules.Inner

variable {B n R size d K : ℕ} {r h : ℤ} (S : Inner B n R size d K r h)

lemma extension_pos : 0 < S.extension := by
  have hl := S.lag_pos
  have he := S.extension_bound
  omega

lemma max_pos (hB : 0 < B) : 0 < S.Hmax :=
  (S.H_pos ⟨0,hB⟩).trans_le (S.H_bounded _)

lemma halfGap_large (hB : 0 < B) (hr : 0 ≤ r) :
    S.Hmax + r < S.halfGap ∧ (B * R : ℕ) + r < S.halfGap := by
  have hp := S.max_pos hB
  have he := S.extension_pos
  have hb := S.gap_bound
  constructor <;> omega

def boundary (j : ℕ) : ℤ := (j + 1 : ℕ) * (2 * S.halfGap)

def mainBase (j : ℕ) : ℤ := (2 * j + 3 : ℕ) * S.halfGap

def mainOffset (j a : ℕ) : ℤ := S.mainBase j + a * B

def periodicOffset (j : ℕ) (u : Fin B) (a : ℕ) : ℤ :=
  S.boundary j + S.H u + S.lag + a * B

lemma main_multiple (j a : ℕ) : (B : ℤ) ∣ S.mainOffset j a := by
  apply dvd_add
  · exact dvd_mul_of_dvd_right S.gap_multiple _
  · exact dvd_mul_left _ _

lemma periodic_multiple (j : ℕ) (u : Fin B) (a : ℕ) :
    (B : ℤ) ∣ S.periodicOffset j u a := by
  apply dvd_add
  · apply dvd_add
    · exact dvd_add (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right S.gap_multiple _) _)
        (S.H_multiple u)
    · exact S.lag_multiple
  · exact dvd_mul_left _ _

lemma main_before (hB : 0 < B) (hr : 0 ≤ r) (i j a : ℕ) (u : Fin B) (hij : i ≤ j) :
    S.boundary i + S.H u + r < S.mainOffset j a := by
  have hh := (S.halfGap_large hB hr).1
  have hwidth := S.H_bounded u
  have hgap := S.gap_pos
  have hi : ((i + 1 : ℕ) : ℤ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.add_le_add_right hij 1
  have hmul := mul_le_mul_of_nonneg_right hi (by positivity : 0 ≤ 2 * S.halfGap)
  have ha : 0 ≤ (a : ℤ) * B := by positivity
  dsimp [boundary,mainOffset,mainBase]
  push_cast at hmul ⊢
  nlinarith

lemma main_after (hB : 0 < B) (hr : 0 ≤ r) (i j a' : ℕ) (k : ℤ)
    (hji : j + 1 ≤ i) (ha : a' < R) :
    k < (k - S.mainBase j - a' * B) + S.boundary i - r := by
  have hh := (S.halfGap_large hB hr).2
  have hgap := S.gap_pos
  have hi : ((j + 2 : ℕ) : ℤ) ≤ (i + 1 : ℕ) := by exact_mod_cast (by omega : j + 2 ≤ i + 1)
  have hmul := mul_le_mul_of_nonneg_right hi (by positivity : 0 ≤ 2 * S.halfGap)
  have hab : (a' : ℤ) * B < (B * R : ℕ) := by
    have hn : a' * B < R * B := Nat.mul_lt_mul_of_pos_right ha hB
    simpa only [Nat.cast_mul, mul_comm] using (show ((a' * B : ℕ) : ℤ) < ((R * B : ℕ) : ℤ) by exact_mod_cast hn)
  dsimp [mainBase,boundary]
  push_cast at hmul hh ⊢
  nlinarith

lemma periodic_before (j a : ℕ) (u : Fin B) :
    S.boundary j + S.H u + r < S.periodicOffset j u a := by
  have hl := S.lag_bound
  have hn : 0 ≤ ((size + 2 : ℕ) : ℤ) * d := by positivity
  have ha : 0 ≤ (a : ℤ) * B := by positivity
  dsimp [periodicOffset]
  omega

end IntegerSchedules.Inner

end GeneralizedStarHeight

end OAI
