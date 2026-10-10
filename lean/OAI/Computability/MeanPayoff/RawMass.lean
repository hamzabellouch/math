import OAI.Computability.MeanPayoff.CallBounds

namespace OAI

namespace MeanPayoff.TreeDevice.Certified.DetMass
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair

abbrev Data := W × List W
abbrev Pair := Data × Data

noncomputable def scale (p q : ℤ) : Code Data Data :=
  (fst ≫ₚ RawBudget.times q) ⋏ₚ (snd ≫ₚ map (RawBudget.times p))
noncomputable def labels : Code Data (List Bool) := envMap Word.lt
noncomputable def products : Code Pair (List W) := ((fst ≫ₚ snd) ⋏ₚ (snd ≫ₚ snd)) ≫ₚ Array.mul
noncomputable def denominator : Code Pair W := ((fst ≫ₚ fst) ⋏ₚ (snd ≫ₚ fst)) ≫ₚ Word.mul
noncomputable def base : Code Pair Bool :=
  ((denominator ⋏ₚ products) ≫ₚ envMap (swap ≫ₚ Word.le) ≫ₚ any Code.id) ≫ₚ Code.not
noncomputable def reweight : Code (Data × List Bool) Data :=
  (fst ≫ₚ fst ≫ₚ RawBudget.times 5) ⋏ₚ
    (((fst ≫ₚ snd) ⋏ₚ snd) ≫ₚ
      zip Array.zero false (Code.branch snd (fst ≫ₚ RawBudget.times 4) (fst ≫ₚ RawBudget.times 8)))

structure Rep {n : ℕ} (a : Fin n → ℚ) (r : Data) : Prop where
  den_pos : 0 < r.1.val
  nums : ∃ ws : Fin n → W, r.2=List.ofFn ws ∧
    (∀ i, 0 < (ws i).val) ∧ ∀ i, a i=((ws i).val:ℚ)/(r.1.val:ℚ)

theorem Rep.positive {n : ℕ} {a : Fin n → ℚ} {r : Data} (h : Rep a r) : ∀ i, 0<a i := by
  obtain ⟨ws,_,hp,he⟩ := h.nums
  intro i
  rw [he]
  exact div_pos (by exact_mod_cast hp i) (by exact_mod_cast h.den_pos)

theorem scale_rep {n : ℕ} {a : Fin n → ℚ} {r : Data} (h : Rep a r)
    {p q : ℤ} (hp : 0<p) (hq : 0<q) :
    Rep (fun i => (p:ℚ)/q*a i) (scale p q r) := by
  obtain ⟨ws,hw,hpos,he⟩ := h.nums
  refine ⟨?_,fun i => RawBudget.times p (ws i),?_,?_,?_⟩
  · change 0 < (RawBudget.times q r.1).val
    simp only [RawBudget.times,Code.comp_eval,Code.pair_eval,Code.id_eval,Word.mul_val,Word.constant_val]
    exact mul_pos h.den_pos hq
  · change List.map _ r.2 = _
    rw [hw,List.map_ofFn]
    rfl
  · intro i
    change 0 < (RawBudget.times p (ws i)).val
    simp only [RawBudget.times,Code.comp_eval,Code.pair_eval,Code.id_eval,Word.mul_val,Word.constant_val]
    exact mul_pos (hpos i) hp
  · intro i
    change (p:ℚ)/q*a i = ((RawBudget.times p (ws i)).val:ℚ)/((RawBudget.times q r.1).val:ℚ)
    simp only [RawBudget.times,Code.comp_eval,Code.pair_eval,Code.id_eval,Word.mul_val,Word.constant_val,Int.cast_mul,he]
    ring

theorem labels_eq {n : ℕ} {a : Fin n → ℚ} {r : Data} (h : Rep a r) :
    labels r = List.ofFn (Label.massLabels a) := by
  obtain ⟨ws,hw,_,he⟩ := h.nums
  change List.map (fun w => Word.lt (r.1,w)) r.2 = _
  rw [hw,List.map_ofFn]
  congr 1
  funext i
  change Word.lt (r.1,ws i) = decide (1<a i)
  rw [Word.lt_eval]
  apply decide_eq_decide.mpr
  rw [he,lt_div_iff₀ (show (0:ℚ)<r.1.val by exact_mod_cast h.den_pos),one_mul]
  exact_mod_cast Iff.rfl

theorem base_eq {n : ℕ} {a b : Fin n → ℚ} {r s : Data} (ha : Rep a r) (hb : Rep b s) :
    base (r,s)=decide (∀ i, 1<a i*b i) := by
  obtain ⟨ws,hw,_,he⟩ := ha.nums
  obtain ⟨vs,hv,_,hf⟩ := hb.nums
  have hden : ∀ i, ((ws i).val*(vs i).val ≤ r.1.val*s.1.val) ↔ a i*b i ≤ 1 := by
    intro i
    rw [he,hf,div_mul_div_comm,div_le_iff₀ (mul_pos
      (show (0:ℚ)<r.1.val by exact_mod_cast ha.den_pos)
      (show (0:ℚ)<s.1.val by exact_mod_cast hb.den_pos)),one_mul]
    exact_mod_cast Iff.rfl
  simp only [base,products,denominator,Code.comp_eval,Code.pair_eval,Code.fst_eval,
    Code.snd_eval,Code.envMap_eval,Code.not_eval,Array.mul,Code.zip_eval,hw,hv,
    Array.zip_ofFn,List.map_ofFn,Code.any,Code.filter_eval,Code.empty_eval,
    Code.swap,Word.le_eval,Word.mul_val]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_not, List.isEmpty_iff, List.filter_eq_nil_iff, List.mem_ofFn,
    decide_eq_true_eq, Code.id_eval]
  simp only [Function.comp_apply,Word.mul_val,forall_exists_index,forall_apply_eq_imp_iff,
    hden,decide_eq_true_eq,not_le]

theorem reweight_rep {n : ℕ} {a : Fin n → ℚ} {r : Data} (ha : Rep a r)
    (ls : Fin n → Bool) : Rep (Label.reweight a ls) (reweight (r,List.ofFn ls)) := by
  obtain ⟨ws,hw,hpos,he⟩ := ha.nums
  let vs := fun i => if ls i then RawBudget.times 4 (ws i) else RawBudget.times 8 (ws i)
  have hv : ∀ i, (vs i).val = (ws i).val*(if ls i then 4 else 8) := by
    intro i
    dsimp [vs]
    cases ls i <;> simp [RawBudget.times]
  refine ⟨?_,vs,?_,?_,?_⟩
  · change 0 < (RawBudget.times 5 r.1).val
    simpa [RawBudget.times] using (mul_pos ha.den_pos (by norm_num : (0:ℤ)<5))
  · change Zip.zip _ _ r.2 (List.ofFn ls) = _
    rw [hw,Array.zip_ofFn]
    rfl
  · intro i
    rw [hv]
    exact mul_pos (hpos i) (by cases ls i <;> norm_num)
  · intro i
    change Label.reweight a ls i = ((vs i).val:ℚ)/((RawBudget.times 5 r.1).val:ℚ)
    rw [hv]
    simp only [RawBudget.times,Code.comp_eval,Code.pair_eval,Code.id_eval,Word.mul_val,Word.constant_val,Int.cast_mul]
    cases h : ls i <;> simp [Label.reweight,h,he] <;> ring

end MeanPayoff.TreeDevice.Certified.DetMass

end OAI
