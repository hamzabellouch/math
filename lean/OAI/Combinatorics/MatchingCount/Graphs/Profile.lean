import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.SumLiftMate

namespace OAI

namespace MatchingFPRAS.Subdivision

open Finset

lemma valid_step_eq_iff {m : ℕ} {U : Finset (Fin m)} {b c : Selection m}
    (hb : Valid U b) (hc : Valid U c) (i : Fin m) :
    b i.castSucc = c i.castSucc ↔ b i.succ = c i.succ := by
  by_cases hi : i ∈ U
  · have hb' := hb i
    have hc' := hc i
    simp only [hi, ↓reduceIte] at hb' hc'
    simp [hb'.1,hb'.2,hc'.1,hc'.2]
  · have hb' : b i.succ = !(b i.castSucc) := by
      apply (bool_ne_iff_eq_not _ _).mp
      simpa only [hi, ↓reduceIte] using hb i
    have hc' : c i.succ = !(c i.castSucc) := by
      apply (bool_ne_iff_eq_not _ _).mp
      simpa only [hi, ↓reduceIte] using hc i
    rw [hb',hc']
    simp

lemma valid_eq_iff_zero {m : ℕ} {U : Finset (Fin m)} {b c : Selection m}
    (hb : Valid U b) (hc : Valid U c) (i : Fin (m+1)) :
    b i = c i ↔ b 0 = c 0 := by
  have aux (k : ℕ) (hk : k < m+1) : b ⟨k,hk⟩ = c ⟨k,hk⟩ ↔ b 0 = c 0 := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have hk' : k < m := by omega
      exact ((valid_step_eq_iff hb hc ⟨k,hk'⟩).symm).trans (ih (by omega))
  exact aux i.val i.isLt

theorem broken_unique {m : ℕ} {U : Finset (Fin m)} (hU : U.Nonempty)
    {b c : Selection m} (hb : Valid U b) (hc : Valid U c) : b = c := by
  obtain ⟨j,hj⟩ := hU
  have hb' := hb j
  have hc' := hc j
  simp only [hj, ↓reduceIte] at hb' hc'
  have hzero := (valid_eq_iff_zero hb hc j.castSucc).mp (hb'.1.trans hc'.1.symm)
  funext i
  exact (valid_eq_iff_zero hb hc i).mpr hzero

noncomputable def profile (p : ℕ) (B Hu Hv lam : ℝ) : List ℝ :=
  duplicate (List.ofFn fun r : Fin p => max B (Hu / 2^r.val)) ++ [lam] ++
    duplicate ((List.ofFn fun r : Fin p => max B (Hv / 2^r.val)).reverse)

@[simp] theorem profile_length (p : ℕ) (B Hu Hv lam : ℝ) :
    (profile p B Hu Hv lam).length = 4*p+1 := by simp [profile]; omega

noncomputable def profileActivity (p : ℕ) (B Hu Hv lam : ℝ) (i : Fin (4*p+1)) : ℝ :=
  (profile p B Hu Hv lam).get (i.cast (profile_length p B Hu Hv lam).symm)

 theorem profileActivity_ofFn (p : ℕ) (B Hu Hv lam : ℝ) :
    List.ofFn (profileActivity p B Hu Hv lam) = profile p B Hu Hv lam := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn, profileActivity, List.get_eq_getElem, Fin.val_cast]

 theorem exact_profile_weight (p : ℕ) (B Hu Hv lam : ℝ) (a : Bool) :
    selectedWeight (profileActivity p B Hu Hv lam)
      (fun i => alternating a i.val) =
        ((∏ r : Fin p, max B (Hu / 2^r.val)) *
         (∏ r : Fin p, max B (Hv / 2^r.val))) * (if a then lam else 1) := by
  rw [intact_weight _ _ (alternating_valid _ _),profileActivity_ofFn]
  simpa [profile,List.prod_ofFn] using
    profile_weight a (List.ofFn fun r : Fin p => max B (Hu / 2^r.val))
      ((List.ofFn fun r : Fin p => max B (Hv / 2^r.val)).reverse) lam

section Deletion

variable {V E : Type*} [Fintype V] [Fintype E]

def Uses {m : ℕ} (u v : E → V) (b : E → Selection m) (e : E) (x : V) : Prop :=
  (b e 0 = true ∧ u e = x) ∨ (b e (Fin.last m) = true ∧ v e = x)

def FamilyHoles (u v : E → V) (m : ℕ) (R₀ : Finset V) (U : E → Finset (Fin m))
    (b : E → Selection m) : Prop :=
  (∀ e, Valid (U e) (b e)) ∧
  (∀ x ∈ R₀, ∀ e, ¬ Uses u v b e x) ∧
  (∀ x ∉ R₀, ∃! e, Uses u v b e x)

noncomputable def broken {m : ℕ} (U : E → Finset (Fin m)) : Finset E := by
  classical
  exact Finset.univ.filter fun e => (U e).Nonempty

@[simp] lemma mem_broken {m : ℕ} (U : E → Finset (Fin m)) (e : E) :
    e ∈ broken U ↔ (U e).Nonempty := by
  classical
  simp [broken]

noncomputable def residualHoles {m : ℕ} (u v : E → V) (R₀ : Finset V)
    (U : E → Finset (Fin m)) (b : E → Selection m) : Finset V := by
  classical
  exact R₀ ∪ Finset.univ.filter (fun x => ∃ e ∈ broken U, Uses u v b e x)

@[simp] lemma mem_residualHoles {m : ℕ} (u v : E → V) (R₀ : Finset V)
    (U : E → Finset (Fin m)) (b : E → Selection m) (x : V) :
    x ∈ residualHoles u v R₀ U b ↔ x ∈ R₀ ∨ ∃ e ∈ broken U, Uses u v b e x := by
  classical
  simp [residualHoles]

theorem residualHoles_independent {m : ℕ} (u v : E → V) (R₀ : Finset V)
    (U : E → Finset (Fin m)) {b c : E → Selection m}
    (hb : FamilyHoles u v m R₀ U b) (hc : FamilyHoles u v m R₀ U c) :
    residualHoles u v R₀ U b = residualHoles u v R₀ U c := by
  classical
  have he (e) (h : e ∈ broken U) : b e = c e :=
    broken_unique ((mem_broken U e).mp h) (hb.1 e) (hc.1 e)
  ext x
  simp only [mem_residualHoles]
  apply or_congr Iff.rfl
  apply exists_congr
  intro e
  constructor <;> rintro ⟨h,hx⟩ <;> refine ⟨h,?_⟩
  · simpa only [Uses,he e h] using hx
  · simpa only [Uses,he e h] using hx

def LogicalHoles (u v : E → V) (R : Finset V) (forbidden : Finset E)
    (s : E → Bool) : Prop :=
  (∀ e ∈ forbidden, s e = false) ∧
  (∀ x ∈ R, ∀ e, ¬ (s e = true ∧ (u e = x ∨ v e = x))) ∧
  (∀ x ∉ R, ∃! e, s e = true ∧ (u e = x ∨ v e = x))

noncomputable def extract {m : ℕ} (U : E → Finset (Fin m))
    (b : E → Selection m) (e : E) : Bool :=
  if (U e).Nonempty then false else b e 0

omit [Fintype V] [Fintype E] in
lemma intact_uses {m : ℕ} (hm : Even m) (u v : E → V) (b : E → Selection m)
    (e : E) (x : V) (hb : Valid ∅ (b e)) :
    Uses u v b e x ↔ b e 0 = true ∧ (u e = x ∨ v e = x) := by
  rw [Uses,intact_terminals hm _ hb]
  exact and_or_left.symm

 theorem extract_legal {m : ℕ} (hm : Even m) (u v : E → V) (R₀ : Finset V)
    (U : E → Finset (Fin m)) (b : E → Selection m)
    (hb : FamilyHoles u v m R₀ U b) :
    LogicalHoles u v (residualHoles u v R₀ U b) (broken U) (extract U b) := by
  classical
  have he (e x) : extract U b e = true ∧ (u e = x ∨ v e = x) ↔
      e ∉ broken U ∧ Uses u v b e x := by
    by_cases h : (U e).Nonempty
    · simp [extract,h]
    · have hu : U e = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      simp only [extract,h,↓reduceIte,mem_broken,not_false_eq_true,true_and]
      exact (intact_uses hm u v b e x (by simpa [hu] using hb.1 e)).symm
  refine ⟨?_,?_,?_⟩
  · intro e he'
    simp [extract,(mem_broken U e).mp he']
  · intro x hx e hxe
    rw [he] at hxe
    rcases (mem_residualHoles u v R₀ U b x).mp hx with hx | ⟨f,hf,hfx⟩
    · exact hb.2.1 x hx e hxe.2
    · have hx0 : x ∉ R₀ := by intro hx0; exact hb.2.1 x hx0 f hfx
      obtain ⟨a,ha,hu⟩ := hb.2.2 x hx0
      have hef : e = f := (hu e hxe.2).trans (hu f hfx).symm
      exact hxe.1 (hef.symm ▸ hf)
  · intro x hx
    have hx0 : x ∉ R₀ := by intro h; exact hx ((mem_residualHoles _ _ _ _ _ _).mpr (Or.inl h))
    obtain ⟨e,he',hu⟩ := hb.2.2 x hx0
    have hn : e ∉ broken U := by
      intro h
      exact hx ((mem_residualHoles _ _ _ _ _ _).mpr (Or.inr ⟨e,h,he'⟩))
    refine ⟨e,(he e x).mpr ⟨hn,he'⟩,?_⟩
    intro f hf
    exact hu f ((he f x).mp hf).2

noncomputable def rebuild {m : ℕ} (U : E → Finset (Fin m))
    (base : E → Selection m) (s : E → Bool) (e : E) : Selection m :=
  if (U e).Nonempty then base e else fun i => alternating (s e) i.val

omit [Fintype V] in
lemma rebuild_uses {m : ℕ} (hm : Even m) (u v : E → V)
    (U : E → Finset (Fin m)) (base : E → Selection m) (s : E → Bool) (e : E) (x : V) :
    Uses u v (rebuild U base s) e x ↔
      (e ∈ broken U ∧ Uses u v base e x) ∨
      (e ∉ broken U ∧ s e = true ∧ (u e = x ∨ v e = x)) := by
  classical
  by_cases h : (U e).Nonempty
  · simp [rebuild,h,Uses]
  · simp [rebuild,h,Uses,alternating,Nat.even_iff.mp hm,and_or_left]

 theorem rebuild_legal {m : ℕ} (hm : Even m) (u v : E → V) (R₀ : Finset V)
    (U : E → Finset (Fin m)) (base : E → Selection m)
    (hb : FamilyHoles u v m R₀ U base) (s : E → Bool)
    (hs : LogicalHoles u v (residualHoles u v R₀ U base) (broken U) s) :
    FamilyHoles u v m R₀ U (rebuild U base s) := by
  classical
  let R := residualHoles u v R₀ U base
  have hu (e x) := rebuild_uses hm u v U base s e x
  refine ⟨?_,?_,?_⟩
  · intro e
    by_cases he : (U e).Nonempty
    · simpa [rebuild,he] using hb.1 e
    · have he' : U e = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      simpa [rebuild,he,he'] using alternating_valid m (s e)
  · intro x hx e he
    have hxR : x ∈ R := (mem_residualHoles _ _ _ _ _ _).mpr (Or.inl hx)
    rcases (hu e x).mp he with ⟨_,he⟩ | ⟨_,he⟩
    · exact hb.2.1 x hx e he
    · exact hs.2.1 x hxR e he
  · intro x hx
    by_cases hxR : x ∈ R
    · obtain hx0 | ⟨e,he,hxe⟩ := (mem_residualHoles _ _ _ _ _ _).mp hxR
      · exact (hx hx0).elim
      obtain ⟨a,ha,hauniq⟩ := hb.2.2 x hx
      refine ⟨e,(hu e x).mpr (Or.inl ⟨he,hxe⟩),?_⟩
      intro f hf
      rcases (hu f x).mp hf with ⟨_,hf⟩ | ⟨_,hf⟩
      · exact (hauniq f hf).trans (hauniq e hxe).symm
      · exact (hs.2.1 x hxR f hf).elim
    · obtain ⟨e,he,heuniq⟩ := hs.2.2 x hxR
      have hen : e ∉ broken U := by
        intro he'
        have := hs.1 e he'
        simp [this] at he
      refine ⟨e,(hu e x).mpr (Or.inr ⟨hen,he⟩),?_⟩
      intro f hf
      rcases (hu f x).mp hf with ⟨hfb,hf⟩ | ⟨_,hf⟩
      · exact (hxR ((mem_residualHoles _ _ _ _ _ _).mpr (Or.inr ⟨f,hfb,hf⟩))).elim
      · exact heuniq f hf

omit [Fintype V] [Fintype E] in
 theorem rebuild_extract [Fintype V] [Fintype E] {m : ℕ} (u v : E → V) (R₀ : Finset V)
    (U : E → Finset (Fin m)) (base b : E → Selection m)
    (hb0 : FamilyHoles u v m R₀ U base) (hb : FamilyHoles u v m R₀ U b) :
    rebuild U base (extract U b) = b := by
  classical
  funext e i
  by_cases he : (U e).Nonempty
  · have hbe := broken_unique he (hb0.1 e) (hb.1 e)
    simp [rebuild,he,hbe]
  · have he' : U e = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    have hl := (intact_iff (b e)).mp (by simpa [he'] using hb.1 e) i
    simpa [rebuild,extract,he] using hl.symm

omit [Fintype V] [Fintype E] in
 theorem extract_rebuild [Fintype V] [Fintype E] {m : ℕ} (u v : E → V) (R : Finset V)
    (U : E → Finset (Fin m)) (base : E → Selection m) (s : E → Bool)
    (hs : LogicalHoles u v R (broken U) s) :
    extract U (rebuild U base s) = s := by
  classical
  funext e
  by_cases he : (U e).Nonempty
  · have hs' := hs.1 e ((mem_broken U e).mpr he)
    simp [extract,he,hs']
  · simp [extract,rebuild,he]

noncomputable def deletionEquiv {m : ℕ} (hm : Even m) (u v : E → V) (R₀ : Finset V)
    (U : E → Finset (Fin m)) (base : E → Selection m)
    (hb : FamilyHoles u v m R₀ U base) :
    {b : E → Selection m // FamilyHoles u v m R₀ U b} ≃
      {s : E → Bool // LogicalHoles u v (residualHoles u v R₀ U base) (broken U) s} where
  toFun b := ⟨extract U b.val, by
    have h := extract_legal hm u v R₀ U b.val b.property
    rwa [residualHoles_independent u v R₀ U b.property hb] at h⟩
  invFun s := ⟨rebuild U base s.val,rebuild_legal hm u v R₀ U base hb s.val s.property⟩
  left_inv b := Subtype.ext (rebuild_extract u v R₀ U base b.val hb b.property)
  right_inv s := Subtype.ext (extract_rebuild u v _ U base s.val s.property)

noncomputable def realHolePartition (u v : E → V) (m : ℕ) (R₀ : Finset V)
    (U : E → Finset (Fin m)) (w : E → Fin (m+1) → ℝ) : ℝ := by
  classical
  letI := Fintype.ofFinite {b : E → Selection m // FamilyHoles u v m R₀ U b}
  exact ∑ b : {b : E → Selection m // FamilyHoles u v m R₀ U b},
    ∏ e, selectedWeight (w e) (b.val e)

noncomputable def logicalHolePartition (u v : E → V) (R : Finset V)
    (forbidden : Finset E) (lam : E → ℝ) : ℝ := by
  classical
  letI := Fintype.ofFinite {s : E → Bool // LogicalHoles u v R forbidden s}
  exact ∑ s : {s : E → Bool // LogicalHoles u v R forbidden s},
    ∏ e, if s.val e then lam e else 1

noncomputable def deletionConstant {m : ℕ} (U : E → Finset (Fin m))
    (base : E → Selection m) (w : E → Fin (m+1) → ℝ) (C : E → ℝ) : ℝ :=
  ∏ e, if (U e).Nonempty then selectedWeight (w e) (base e) else C e

omit [Fintype V] [Fintype E] in
 theorem deletion_weight [Fintype V] [Fintype E] {m : ℕ} (u v : E → V) (R₀ : Finset V)
    (U : E → Finset (Fin m)) (base b : E → Selection m)
    (hb0 : FamilyHoles u v m R₀ U base) (hb : FamilyHoles u v m R₀ U b)
    (w : E → Fin (m+1) → ℝ) (left right : E → List ℝ) (lam : E → ℝ)
    (hw : ∀ e, List.ofFn (w e) = duplicate (left e) ++ [lam e] ++ duplicate (right e)) :
    (∏ e, selectedWeight (w e) (b e)) =
      deletionConstant U base w (fun e => (left e).prod * (right e).prod) *
        ∏ e, if extract U b e then lam e else 1 := by
  classical
  unfold deletionConstant
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  by_cases he : (U e).Nonempty
  · have heq := broken_unique he (hb0.1 e) (hb.1 e)
    simp [extract,he,heq]
  · have he' : U e = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp only [extract,he,↓reduceIte]
    rw [intact_weight _ _ (by simpa [he'] using hb.1 e),hw e,profile_weight]

theorem deletion_partition_identity {m : ℕ} (hm : Even m) (u v : E → V) (R₀ : Finset V)
    (U : E → Finset (Fin m)) (base : E → Selection m)
    (hb : FamilyHoles u v m R₀ U base)
    (w : E → Fin (m+1) → ℝ) (left right : E → List ℝ) (lam : E → ℝ)
    (hw : ∀ e, List.ofFn (w e) = duplicate (left e) ++ [lam e] ++ duplicate (right e)) :
    realHolePartition u v m R₀ U w =
      deletionConstant U base w (fun e => (left e).prod * (right e).prod) *
        logicalHolePartition u v (residualHoles u v R₀ U base) (broken U) lam := by
  classical
  let := Fintype.ofFinite {b : E → Selection m // FamilyHoles u v m R₀ U b}
  let := Fintype.ofFinite {s : E → Bool //
    LogicalHoles u v (residualHoles u v R₀ U base) (broken U) s}
  unfold realHolePartition logicalHolePartition
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv (deletionEquiv hm u v R₀ U base hb)
  intro b
  exact deletion_weight u v R₀ U base b.val hb b.property w left right lam hw

end Deletion

theorem selectedWeight_vertex_factor {m : ℕ} (U : Finset (Fin m))
    (b : Selection m) (hb : Valid U b) (z : Fin (m+2) → ℝ) :
    selectedWeight (fun i => z i.castSucc * z i.succ) b =
      (if b 0 then z 0 else 1) * (if b (Fin.last m) then z (Fin.last (m+1)) else 1) *
        ∏ i : Fin m, if i ∈ U then 1 else z i.succ.castSucc := by
  classical
  unfold selectedWeight
  have hsplit (i : Fin (m+1)) :
      (if b i then z i.castSucc * z i.succ else 1) =
      (if b i then z i.castSucc else 1) * (if b i then z i.succ else 1) := by
    cases b i <;> simp
  simp_rw [hsplit]
  rw [Finset.prod_mul_distrib,
    Fin.prod_univ_succ (fun i : Fin (m+1) => if b i then z i.castSucc else 1),
    Fin.prod_univ_castSucc (fun i : Fin (m+1) => if b i then z i.succ else 1)]
  have he : ∀ i : Fin m,
      (if b i.succ then z i.succ.castSucc else 1) *
        (if b i.castSucc then z i.castSucc.succ else 1) =
      if i ∈ U then 1 else z i.succ.castSucc := by
    intro i
    have hz : i.castSucc.succ = i.succ.castSucc := rfl
    rw [hz]
    have h := hb i
    by_cases hi : i ∈ U
    · simp only [hi,↓reduceIte] at h ⊢
      simp [h.1,h.2]
    · simp only [hi,↓reduceIte] at h ⊢
      cases h₁ : b i.castSucc <;> cases h₂ : b i.succ <;> simp_all
  calc
    _ = (if b 0 then z 0 else 1) * (if b (Fin.last m) then z (Fin.last (m+1)) else 1) *
        ∏ i : Fin m, ((if b i.succ then z i.succ.castSucc else 1) *
          (if b i.castSucc then z i.castSucc.succ else 1)) := by
      rw [Finset.prod_mul_distrib]
      simp only [Fin.castSucc_zero, Fin.succ_last]
      ring
    _ = _ := by simp_rw [he]

theorem valid_interval {m : ℕ} {U : Finset (Fin m)} {b : Selection m}
    (hb : Valid U b) (a k : ℕ) (hak : a+k ≤ m)
    (hfree : ∀ i : Fin m, a ≤ i.val → i.val < a+k → i ∉ U) :
    b ⟨a+k,by omega⟩ = alternating (b ⟨a,by omega⟩) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hai : a+k < m := by omega
    have hf := hb ⟨a+k,hai⟩
    simp only [hfree ⟨a+k,hai⟩ (by dsimp; omega) (by dsimp; omega),↓reduceIte] at hf
    have he := (bool_ne_iff_eq_not _ _).mp hf
    have hi := ih (by omega) (fun i hi hj => hfree i hi (by omega))
    simpa only [Fin.succ_mk, Fin.castSucc_mk, Nat.add_assoc,
      alternating_succ, hi] using he

theorem first_hole_terminal {m : ℕ} {U : Finset (Fin m)} {b : Selection m}
    (hb : Valid U b) (j : Fin m) (hj : j ∈ U)
    (hfirst : ∀ i ∈ U, j ≤ i) :
    b 0 = true ↔ j.val % 2 = 1 := by
  have hv := valid_interval hb 0 j.val (by omega) (by
    intro i hi hij him
    have hh := hfirst i him
    have : j.val ≤ i.val := hh
    omega)
  have hz : b j.castSucc = false := by
    have h := hb j
    simp only [hj,↓reduceIte] at h
    exact h.1
  have he : b j.castSucc = alternating (b 0) j.val := by
    have ez : (⟨0,by omega⟩ : Fin (m+1)) = 0 := Fin.ext rfl
    have ee : (⟨0+j.val,by omega⟩ : Fin (m+1)) = j.castSucc := by
      apply Fin.ext; dsimp; omega
    rw [ee,ez] at hv
    exact hv
  rw [hz] at he
  by_cases h : j.val%2=0
  · simp only [alternating,h,↓reduceIte] at he
    simp [← he,h]
  · have h1 : j.val%2=1 := by omega
    simp only [alternating,h,↓reduceIte] at he
    cases hbool : b 0
    · rw [hbool] at he; contradiction
    · simp only [h1]

end MatchingFPRAS.Subdivision

end OAI
