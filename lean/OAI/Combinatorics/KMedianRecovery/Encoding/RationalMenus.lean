import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.LeafDistances
import OAI.Combinatorics.KMedianRecovery.Branching.PopulationBridge
import OAI.Combinatorics.KMedianRecovery.Sampling.RationalSampling

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine
variable {n : ℕ}
def leafValues (δ : Fin n→Fin n→ℚ) (s : State n) (w : Fin n) : List ℚ :=
  s.leaves.map (fun z=>δ w z.1+z.2)
def nearestLeaf (δ : Fin n→Fin n→ℚ) (s : State n) (w : Fin n) : Option ℚ :=
  if s.leaves=[] then none else some (RationalMin.minimum (leafValues δ s w))
def menuWeight (M E J : ℕ) : Sampling.Entry M E J → ℚ
  | .inl _=>1/(3*M)
  | .inr (.inl _)=>1/(3*(E+1))
  | .inr (.inr j)=>(1/3)*((1/2:ℚ)^(j.val+1)/(1-(1/2:ℚ)^J))
lemma menuWeight_cast (M E J : ℕ) (e : Sampling.Entry M E J) :
    (menuWeight M E J e:ℝ)=RadiusMenus.menuWeight M E J e := by
  rcases e with i | (i | i) <;>
    simp only [menuWeight,RadiusMenus.menuWeight,RadiusMenus.thirdNormalizer_eq,Rat.cast_div,Rat.cast_mul,
      Rat.cast_one,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_add,Rat.cast_pow,Rat.cast_sub]
section Metric
variable [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
include hδ
omit hδ [PseudoMetricSpace (Fin n)] in
lemma leaves_empty_iff (s : State n) : s.real.leaves=[] ↔ s.leaves=[] := List.map_eq_nil_iff
omit hδ [PseudoMetricSpace (Fin n)] in
lemma leafValues_nonempty (s : State n) (w : Fin n) (h : s.leaves≠[]) : leafValues δ s w≠[] := by
  exact fun hh=>h (List.map_eq_nil_iff.mp hh)
lemma nearestLeaf_cast (s : State n) (w : Fin n) :
    (nearestLeaf δ s w).map (fun q : ℚ=>(q:ℝ))=Sampling.nearestLeaf s.real w := by
  by_cases he : s.leaves=[]
  · simp [nearestLeaf,he,Sampling.nearestLeaf,Sampling.leafDistances,State.real]
  · have hn : (Sampling.leafDistances s.real w).Nonempty := by
      obtain ⟨z,hz⟩:=List.exists_mem_of_ne_nil s.leaves he
      exact ⟨dist w z.1+(z.2:ℝ),Finset.mem_image.mpr ⟨(z.1,(z.2:ℝ)),List.mem_toFinset.mpr
        (List.mem_map.mpr ⟨z,hz,rfl⟩),rfl⟩⟩
    simp only [nearestLeaf,ite_eq_right he,Option.map_some,Sampling.nearestLeaf,dite_eq_left hn,Option.some.injEq]
    apply le_antisymm
    · apply Finset.le_inf'
      intro x hx
      obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hx
      obtain ⟨t,ht,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp hz)
      dsimp only [id]
      rw [←hδ w t.1,←Rat.cast_add]
      exact_mod_cast RationalMin.minimum_le_mem (leafValues δ s w) (δ w t.1+t.2) (List.mem_map.mpr ⟨t,ht,rfl⟩)
    · apply RationalMin.minimum_lower_real
      · exact leafValues_nonempty δ s w he
      · intro q hq
        obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hq
        rw [Rat.cast_add,hδ]
        exact Finset.inf'_le _ (Finset.mem_image.mpr ⟨(z.1,(z.2:ℝ)),List.mem_toFinset.mpr (List.mem_map.mpr ⟨z,hz,rfl⟩),rfl⟩)
def menuRadius (D : Finset (Fin n)) (P κ : ℚ) (m M E J : ℕ) (s : State n) (w : Fin n) :
    Sampling.Entry M E J → Option ℚ
  | .inl j=>some ((j.val+1)*κ*BinaryPopulation.radiusQ P m (BinaryPopulation.distanceList δ D w))
  | .inr (.inl e)=>(nearestLeaf δ s w).map (fun r=>r/(1+κ)^e.val)
  | .inr (.inr j)=>some ((j.val+1)*κ*BinaryPopulation.radiusQ P m (BinaryPopulation.distanceList δ D w))
lemma menuRadius_cast (D : Finset (Fin n)) (hD : D.Nonempty) (P κ : ℚ) (m M E J : ℕ) (s : State n) (w : Fin n)
    (e : Sampling.Entry M E J) :
    (menuRadius δ D P κ m M E J s w e).map (fun q : ℚ=>(q:ℝ))=
      Sampling.menuRadius D hD (P:ℝ) (κ:ℝ) m M E J s.real w e := by
  rcases e with i | (i | i)
  · simp only [menuRadius,Sampling.menuRadius,Option.map_some,Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,
      Rat.cast_one,BinaryPopulation.radiusQ_cast δ hδ D hD]
  · simp only [menuRadius,Sampling.menuRadius,←nearestLeaf_cast δ hδ,Option.map_map,Function.comp_def,
      Rat.cast_div,Rat.cast_pow,Rat.cast_add,Rat.cast_one]
  · simp only [menuRadius,Sampling.menuRadius,Option.map_some,Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,
      Rat.cast_one,BinaryPopulation.radiusQ_cast δ hδ D hD]
end Metric
end MetricKMedianRecovery.RationalSampling

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine
variable {n : ℕ}
noncomputable def chosenKey (δ : Fin n→Fin n→ℚ) (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) : ℚ×ₗℕ :=
  (keys δ S Δ s w).min' (keys_nonempty δ S Δ s w)
noncomputable def reference (δ : Fin n→Fin n→ℚ) (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) : ℚ :=
  (ofLex (chosenKey δ S Δ s w)).1
noncomputable def chosenId (δ : Fin n→Fin n→ℚ) (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) : ℕ :=
  (ofLex (chosenKey δ S Δ s w)).2
noncomputable def clientWeight (δ : Fin n→Fin n→ℚ) (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) : ℚ :=
  max 0 (reference δ S Δ s w)
noncomputable def totalWeight (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : State n) : ℚ :=
  ∑ w∈D,clientWeight δ S Δ s w
noncomputable def transitionWeight (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (M E J : ℕ)
    (s : Option (State n)) (a : Sampling.Action D M E J) : ℚ :=
  match s with
  | none=>if a=Sum.inl () then 1 else 0
  | some s=>if 0<totalWeight δ D S Δ s then
      match a with
      | .inl _=>0
      | .inr (.inl w)=>clientWeight δ S Δ s w/(2*totalWeight δ D S Δ s)
      | .inr (.inr (w,e))=>clientWeight δ S Δ s w/(2*totalWeight δ D S Δ s)*menuWeight M E J e
    else if a=Sum.inl () then 1 else 0
def State.remove (s : State n) (v : Fin n) : State n := ⟨insert v s.deleted,s.leaves⟩
def State.add (s : State n) (w : Fin n) (R : ℚ) : State n := ⟨s.deleted,s.leaves++[(w,R)]⟩
def retain (m : ℕ) (s : State n) : Option (State n) :=
  if s.leaves.length ≤ m ∧ s.deleted.card ≤ m then some s else none
lemma remove_real (s : State n) (v : Fin n) : (s.remove v).real=s.real.remove v := by
  simp only [State.remove,State.real,Sampling.State.remove]
  congr 1
  ext x
  simp only [Finset.mem_insert]
lemma add_real (s : State n) (w : Fin n) (R : ℚ) : (s.add w R).real=s.real.add w (R:ℝ) := by
  simp only [State.add,State.real,Sampling.State.add,List.map_append,List.map_cons,List.map_nil]
lemma retain_real (m : ℕ) (s : State n) : (retain m s).map State.real=Sampling.retain m s.real := by
  simp only [retain,Sampling.retain,State.real,List.length_map]
  split_ifs <;> rfl
noncomputable def update (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ)
    (m M E J : ℕ) (s : Option (State n)) (a : Sampling.Action D M E J) : Option (State n) :=
  match s with
  | none=>none
  | some s=>if 0<totalWeight δ D S Δ s then
      match a with
      | .inl _=>none
      | .inr (.inl w)=>if h : chosenId δ S Δ s w<n then retain m (s.remove ⟨chosenId δ S Δ s w,h⟩) else none
      | .inr (.inr (w,e))=>match menuRadius δ D P κ m M E J s w e with
        | none=>none
        | some R=>if (F.filter (fun v=>δ w.val v≤R)).Nonempty then retain m (s.add w R) else none
    else none
section Metric
variable [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
include hδ
lemma reference_cast (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) :
    (reference δ S Δ s w:ℝ)=Sampling.reference S (Δ:ℝ) s.real w := minimum_reference δ hδ S Δ s w
lemma chosenId_eq (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) :
    chosenId δ S Δ s w=tagId (Sampling.chosen S (Δ:ℝ) s.real w) := by
  simp only [chosenId,chosenKey,minimum_key δ hδ,key,ofLex_toLex]
lemma clientWeight_cast (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) :
    (clientWeight δ S Δ s w:ℝ)=Sampling.clientWeight S (Δ:ℝ) s.real w := by
  simp only [clientWeight,Rat.cast_max,Rat.cast_zero,reference_cast δ hδ,Sampling.clientWeight]
lemma totalWeight_cast (D S : Finset (Fin n)) (Δ : ℚ) (s : State n) :
    (totalWeight δ D S Δ s:ℝ)=Sampling.totalWeight D S (Δ:ℝ) s.real := by
  simp only [totalWeight,Rat.cast_sum,clientWeight_cast δ hδ,Sampling.totalWeight]
lemma transitionWeight_cast (D S : Finset (Fin n)) (Δ : ℚ) (M E J : ℕ) (s : Option (State n))
    (a : Sampling.Action D M E J) :
    (transitionWeight δ D S Δ M E J s a:ℝ)=Sampling.transitionWeight D S (Δ:ℝ) M E J (s.map State.real) a := by
  cases s with
  | none=>simp only [transitionWeight,Sampling.transitionWeight,Option.map_none];split_ifs <;> norm_num
  | some s=>
    simp only [transitionWeight,Sampling.transitionWeight,Option.map_some,←totalWeight_cast δ hδ]
    have hh : (0:ℝ)<(totalWeight δ D S Δ s:ℝ) ↔ 0<totalWeight δ D S Δ s := Rat.cast_pos
    simp only [hh]
    split_ifs
    · rcases a with u | (w | ⟨w,e⟩) <;>
        simp only [Rat.cast_zero,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,clientWeight_cast δ hδ,menuWeight_cast]
    all_goals norm_num
lemma update_real (D F S : Finset (Fin n)) (hD : D.Nonempty) (Δ P κ : ℚ) (m M E J : ℕ)
    (s : Option (State n)) (a : Sampling.Action D M E J) :
    (update δ D F S Δ P κ m M E J s a).map State.real=
      Sampling.update D F S hD (Δ:ℝ) (P:ℝ) (κ:ℝ) m M E J (s.map State.real) a := by
  cases s with
  | none=>rfl
  | some s=>
    simp only [update,Sampling.update,Option.map_some,←totalWeight_cast δ hδ]
    have hh : (0:ℝ)<(totalWeight δ D S Δ s:ℝ) ↔ 0<totalWeight δ D S Δ s := Rat.cast_pos
    simp only [hh]
    split_ifs with ht
    · rcases a with u | (w | ⟨w,e⟩)
      · rfl
      · dsimp only
        rw [chosenId_eq δ hδ]
        cases hz : ofLex (Sampling.chosen S (Δ:ℝ) s.real w) with
        | inl v=>
          simp only [tagId,hz,dite_eq_left v.isLt,retain_real,remove_real]
        | inr j=>simp [tagId,hz,show ¬n+j<n by omega]
      · dsimp only
        have hr:=menuRadius_cast δ hδ D hD P κ m M E J s w e
        cases he : menuRadius δ D P κ m M E J s w e with
        | none=>simp only [Option.map_none,he] at hr;rw [←hr];rfl
        | some R=>
          simp only [he,Option.map_some] at hr
          rw [←hr]
          have hb : F.filter (fun v=>δ w.val v≤R)=F.filter (fun v=>dist w.val v≤(R:ℝ)) := by
            ext i
            simp only [Finset.mem_filter,←hδ w.val i,Rat.cast_le]
          dsimp only
          rw [hb]
          split_ifs <;> simp only [retain_real,add_real,Option.map_none]
    · rfl
end Metric
end MetricKMedianRecovery.RationalSampling

end OAI
