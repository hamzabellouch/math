import OAI.Combinatorics.HoneycombChords.Occupancy

namespace OAI

/-!
# Orientations and tensor coefficients of chords

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

namespace CriticalHoneycomb.Transfer.ChordOrientations
open PhysicalTiles CenterPartition
open scoped BigOperators

/-- A literal simple honeycomb path, including its two exterior endpoint
centers. It will be applied only when those endpoints lie outside the rectangle. -/
structure CenterPath (n : ℕ) where
  point : Fin (n+2) → Center
  injective : Function.Injective point
  side : Fin (n+1) → Fin 3
  step : ∀ i, neighbor (point i.castSucc) (side i)=point i.succ

def CenterPath.edge {n : ℕ} (p : CenterPath n) (i : Fin (n+1)) : Wire :=
  incidentWire (p.point i.castSucc) (p.side i)

lemma CenterPath.edge_injective {n : ℕ} (p : CenterPath n) : Function.Injective p.edge := by
  intro i j he
  obtain ⟨hs,hv|hv⟩ := (incidentWire_eq_iff _ _ _ _).mp he
  · have hi := p.injective hv
    exact Fin.ext (congrArg (fun x : Fin (n+2)=>x.val) hi)
  · have h1 : p.point i.succ=p.point j.castSucc := (p.step i).symm.trans hv
    have h2 : p.point j.succ=p.point i.castSucc := by
      rw [←p.step j,←hs,←hv,neighbor_neighbor]
    have h1' := congrArg Fin.val (p.injective h1)
    have h2' := congrArg Fin.val (p.injective h2)
    simp only [Fin.val_succ,Fin.val_castSucc] at h1' h2'
    omega

/-- Spin zero follows the positive source wire direction: west out of an
up center, and middle/south into it. Spin two is the reverse direction. -/
def outSpin (v : Center) (k : Fin 3) : Fin 3 :=
  if v.2.2=decide (k=2) then 0 else 2

def inSpin (v : Center) (k : Fin 3) : Fin 3 :=
  if v.2.2=decide (k=2) then 2 else 0

lemma outSpin_neighbor (v : Center) (k : Fin 3) :
    outSpin (neighbor v k) k=inSpin v k := by
  rcases v with ⟨i,j,b⟩
  cases b <;> fin_cases k <;> simp [outSpin,inSpin,neighbor,up,down]

lemma inSpin_neighbor (v : Center) (k : Fin 3) :
    inSpin (neighbor v k) k=outSpin v k := by
  rw [←outSpin_neighbor,neighbor_neighbor]

lemma outSpin_ne_empty (v : Center) (k : Fin 3) : outSpin v k≠1 := by
  unfold outSpin; split_ifs <;> decide

noncomputable def CenterPath.spins {n : ℕ} (p : CenterPath n) : Wire → Fin 3 :=
  Function.extend p.edge (fun i=>outSpin (p.point i.castSucc) (p.side i)) (fun _=>1)

lemma CenterPath.spins_edge {n : ℕ} (p : CenterPath n) (i : Fin (n+1)) :
    p.spins (p.edge i)=outSpin (p.point i.castSucc) (p.side i) :=
  p.edge_injective.extend_apply _ _ _

lemma CenterPath.spins_off {n : ℕ} (p : CenterPath n) (w : Wire)
    (hw : w ∉ Set.range p.edge) : p.spins w=1 := by
  exact Function.extend_apply' _ _ _ hw

def CenterPath.center {n : ℕ} (p : CenterPath n) (i : Fin n) : Center :=
  p.point i.castSucc.succ

lemma CenterPath.in_wire {n : ℕ} (p : CenterPath n) (i : Fin n) :
    incidentWire (p.center i) (p.side i.castSucc)=p.edge i.castSucc := by
  change incidentWire (p.point i.castSucc.succ) _ = _
  rw [←p.step i.castSucc,incidentWire_neighbor]
  rfl

lemma CenterPath.out_wire {n : ℕ} (p : CenterPath n) (i : Fin n) :
    incidentWire (p.center i) (p.side i.succ)=p.edge i.succ := by rfl

lemma CenterPath.sides_distinct {n : ℕ} (p : CenterPath n) (i : Fin n) :
    p.side i.castSucc ≠ p.side i.succ := by
  intro he
  have hw : p.edge i.castSucc=p.edge i.succ := by
    rw [←p.in_wire i,←p.out_wire i,he]
  have hi := congrArg Fin.val (p.edge_injective hw)
  simp only [Fin.val_castSucc,Fin.val_succ] at hi
  omega

lemma CenterPath.incident_edge_iff {n : ℕ} (p : CenterPath n) (i : Fin n) (k : Fin 3) :
    incidentWire (p.center i) k ∈ Set.range p.edge ↔
      k=p.side i.castSucc ∨ k=p.side i.succ := by
  constructor
  · rintro ⟨j,hj⟩
    obtain ⟨hk,he|he⟩ := (incidentWire_eq_iff _ _ _ _).mp hj
    · right
      have hi : j=i.succ := by
        apply Fin.ext
        have hh := congrArg Fin.val (p.injective he)
        simpa [CenterPath.center] using hh
      simpa [hi] using hk.symm
    · left
      have hi : j=i.castSucc := by
        apply Fin.ext
        rw [p.step j] at he
        have hh := congrArg Fin.val (p.injective he)
        simp only [Fin.val_succ,Fin.val_castSucc] at hh
        change j.val=i.val
        omega
      simpa [hi] using hk.symm
  · rintro (rfl|rfl)
    · exact ⟨i.castSucc,(p.in_wire i).symm⟩
    · exact ⟨i.succ,(p.out_wire i).symm⟩

lemma CenterPath.spins_local {n : ℕ} (p : CenterPath n) (i : Fin n) (k : Fin 3) :
    p.spins (incidentWire (p.center i) k) =
      if k=p.side i.castSucc then inSpin (p.center i) k
      else if k=p.side i.succ then outSpin (p.center i) k else 1 := by
  split_ifs with hin hout
  · subst k
    rw [p.in_wire i,p.spins_edge]
    change _ = inSpin (p.point i.castSucc.succ) _
    rw [←p.step i.castSucc,inSpin_neighbor]
  · subst k
    rw [p.out_wire i,p.spins_edge]
    rfl
  · apply p.spins_off
    rw [p.incident_edge_iff]
    tauto

noncomputable def localTensor (v : Center) (s : Fin 3 → Fin 3) : ℂ :=
  if v.2.2 then upTensor (s 2) (s 1) (s 0) else downTensor (s 2) (s 1) (s 0)

lemma localTensor_passage_nonzero (v : Center) (a b : Fin 3) (hab : a≠b) :
    localTensor v (fun k=>if k=a then inSpin v k else if k=b then outSpin v k else 1) ≠ 0 := by
  have hk : (kappa:ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact (Real.rpow_pos_of_pos (by positivity : 0<(2+Real.sqrt 2:ℝ)) (-(1:ℝ)/2)).ne'
  rcases v with ⟨i,j,t⟩
  cases t <;> fin_cases a <;> fin_cases b <;>
    simp_all [localTensor,inSpin,outSpin,upTensor,downTensor,Planar.empty,
      Planar.occupied,Planar.cup,Planar.phase_ne_zero]

/-- The orientation directed along an actual simple center path has nonzero
local weight at every visited center. All positions and slot orders are literal. -/
theorem CenterPath.center_nonzero {n : ℕ} (p : CenterPath n) (i : Fin n) :
    centerTensor p.spins (p.center i) ≠ 0 := by
  have he : centerTensor p.spins (p.center i) = localTensor (p.center i)
      (fun k=>if k=p.side i.castSucc then inSpin (p.center i) k
        else if k=p.side i.succ then outSpin (p.center i) k else 1) := by
    unfold centerTensor localTensor
    simp_rw [p.spins_local]
  rw [he]
  exact localTensor_passage_nonzero _ _ _ (p.sides_distinct i)

lemma localTensor_propagate (v : Center) (a b : Fin 3) (hab : a≠b) (s : Fin 3) :
    localTensor v (fun k=>if k=a then inSpin v k else if k=b then s else 1) ≠ 0 ↔
      s=outSpin v b := by
  have hk : (kappa:ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact (Real.rpow_pos_of_pos (by positivity : 0<(2+Real.sqrt 2:ℝ)) (-(1:ℝ)/2)).ne'
  rcases v with ⟨i,j,t⟩
  cases t <;> fin_cases a <;> fin_cases b <;> fin_cases s <;>
    simp_all [localTensor,inSpin,outSpin,upTensor,downTensor,Planar.empty,
      Planar.occupied,Planar.cup,Planar.phase_ne_zero]

/-- The local tensor along the actual ordered center path, with two selected
wires and all other wires vacant. -/
noncomputable def CenterPath.factor {n : ℕ} (p : CenterPath n) (i : Fin n)
    (σ : Fin (n+1) → Fin 3) : ℂ :=
  localTensor (p.center i) (fun k=>if k=p.side i.castSucc then σ i.castSucc
    else if k=p.side i.succ then σ i.succ else 1)

lemma CenterPath.in_direction {n : ℕ} (p : CenterPath n) (i : Fin n) :
    outSpin (p.point i.castSucc.castSucc) (p.side i.castSucc)=
      inSpin (p.center i) (p.side i.castSucc) := by
  change _=inSpin (p.point i.castSucc.succ) _
  rw [←p.step i.castSucc,inSpin_neighbor]

lemma CenterPath.factor_true {n : ℕ} (p : CenterPath n) (i : Fin n) :
    p.factor i (fun j=>outSpin (p.point j.castSucc) (p.side j))=
      centerTensor p.spins (p.center i) := by
  change p.factor i _ = localTensor (p.center i) (fun k=>p.spins (incidentWire (p.center i) k))
  unfold CenterPath.factor
  have he := p.in_direction i
  have he' : p.point i.succ.castSucc = p.center i := rfl
  dsimp only
  rw [he,he']
  congr 1
  funext k
  rw [p.spins_local]
  split_ifs <;> simp_all

/-- Orientation propagates along every actual simple center path. Thus the
boundary condition at the first wire determines all occupied wire labels. -/
theorem CenterPath.orientation_unique {n : ℕ} (p : CenterPath n)
    (σ : Fin (n+1) → Fin 3)
    (hroot : σ 0=outSpin (p.point 0) (p.side 0))
    (hf : ∀ i, p.factor i σ≠0) :
    σ=(fun i=>outSpin (p.point i.castSucc) (p.side i)) := by
  funext i
  induction i using Fin.induction with
  | zero => exact hroot
  | succ i ih =>
    have hh := hf i
    unfold CenterPath.factor at hh
    rw [ih,p.in_direction i] at hh
    have he : (fun k=>if k=p.side i.castSucc then inSpin (p.center i) (p.side i.castSucc)
        else if k=p.side i.succ then σ i.succ else 1) =
        (fun k=>if k=p.side i.castSucc then inSpin (p.center i) k
        else if k=p.side i.succ then σ i.succ else 1) := by
      funext k; split_ifs <;> simp_all
    rw [he] at hh
    have hc := (localTensor_propagate (p.center i) _ _ (p.sides_distinct i) (σ i.succ)).mp hh
    exact hc

/-- Literal finite orientation contraction of the actual path, with fixed
source arrow and the final arrow summed (it will necessarily be the through
arrow). This is not a new abstract kernel substituted for the center model. -/
noncomputable def CenterPath.orientationSum {n : ℕ} (p : CenterPath n) : ℂ := by
  classical
  exact ∑ σ : Fin (n+1) → Fin 3,
    if σ 0=outSpin (p.point 0) (p.side 0) then ∏ i, p.factor i σ else 0

/-- There is exactly one contributing orientation for a loop-free chord. -/
theorem CenterPath.orientationSum_eq {n : ℕ} (p : CenterPath n) :
    p.orientationSum=∏ i, centerTensor p.spins (p.center i) := by
  classical
  unfold CenterPath.orientationSum
  rw [Finset.sum_eq_single (fun i=>outSpin (p.point i.castSucc) (p.side i))]
  · simp only [Fin.castSucc_zero]
    exact Finset.prod_congr rfl (fun i _=>p.factor_true i)
  · intro σ hσ hne
    split_ifs with hr
    · by_contra hh
      exact hne (p.orientation_unique σ hr (fun i=>(Finset.prod_ne_zero_iff.mp hh) i (Finset.mem_univ i)))
    · rfl
  · simp

/-- Noncancellation for a literal loop-free honeycomb center chord, rather
than only for an abstract strand or a tensor with assumed coefficient. -/
theorem CenterPath.orientationSum_ne_zero {n : ℕ} (p : CenterPath n) :
    p.orientationSum≠0 := by
  rw [p.orientationSum_eq]
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>p.center_nonzero i)

end CriticalHoneycomb.Transfer.ChordOrientations
namespace CriticalHoneycomb.Transfer.ChordOrientations

variable {D : Set Center} {a b : Port D}

def extendedTrace (γ : Chord D a b) : List Center :=
  a.outside :: (γ.val ++ [b.outside])

lemma extendedTrace_length (γ : Chord D a b) :
    (extendedTrace γ).length=γ.val.length+2 := by simp [extendedTrace,Nat.add_assoc]

lemma extendedTrace_nodup (γ : Chord D a b) (hab : a.outside≠b.outside) :
    (extendedTrace γ).Nodup := by
  have ha : a.outside ∉ γ.val := fun h=>a.outside_not_mem (γ.property.1.2.2 _ h)
  have hb : b.outside ∉ γ.val := fun h=>b.outside_not_mem (γ.property.1.2.2 _ h)
  rw [extendedTrace,List.nodup_cons,List.nodup_append]
  refine ⟨by simpa using ⟨ha,hab⟩,γ.property.1.1,by simp,?_⟩
  intro x hx y hy
  have he : y=b.outside := by simpa using hy
  subst y
  intro he
  exact hb (he ▸ hx)

lemma extendedTrace_chain (γ : Chord D a b) :
    List.IsChain Adj (extendedTrace γ) := by
  have hc : List.IsChain Adj (a.outside::γ.val) := by
    rw [List.isChain_cons]
    refine ⟨?_,γ.property.1.2.1⟩
    rw [γ.property.2.1]
    intro y hy
    have he : a.inside=y := Option.mem_some_iff.mp hy
    subst y
    exact FiniteConfigurations.adj_symmetric a.adjacent
  have hn : γ.val≠[] := by
    intro he
    have hh := γ.property.2.2
    simp [he] at hh
  change List.IsChain Adj ((a.outside::γ.val)++[b.outside])
  apply List.IsChain.append hc (by simp)
  intro x hx y hy
  have hx' : x=b.inside := by
    have hh : (a.outside::γ.val).getLast?=some b.inside := by
      rw [List.getLast?_cons_of_ne_nil hn,γ.property.2.2]
    symm
    simpa [hh] using hx
  have hy' : y=b.outside := by symm; simpa using hy
  subst x; subst y
  exact b.adjacent

/-- Conversion of an actual simple chord (with its unweighted boundary
ports) to the ordered-center model used in the tensor noncancellation proof. -/
noncomputable def ofChord (γ : Chord D a b) (hab : a.outside≠b.outside) :
    CenterPath γ.val.length := by
  let x : Fin (γ.val.length+2) → Center := fun i=>
    (extendedTrace γ).get ⟨i.val,by rw [extendedTrace_length]; exact i.isLt⟩
  have hinj : Function.Injective x := by
    intro i j he
    have hh := (extendedTrace_nodup γ hab).get_inj_iff.mp he
    exact Fin.ext (congrArg (fun z : Fin (extendedTrace γ).length=>z.val) hh)
  have hc (i : Fin (γ.val.length+1)) : Adj (x i.castSucc) (x i.succ) := by
    exact (List.isChain_iff_getElem.mp (extendedTrace_chain γ)) i.val
      (by rw [extendedTrace_length]; omega)
  exact ⟨x,hinj,fun i=>((adj_iff_neighbor _ _).mp (hc i)).choose,
    fun i=>((adj_iff_neighbor _ _).mp (hc i)).choose_spec⟩

lemma ofChord_point (γ : Chord D a b) (hab : a.outside≠b.outside)
    (i : Fin (γ.val.length+2)) :
    (ofChord γ hab).point i=(extendedTrace γ)[i.val]'(by rw [extendedTrace_length]; exact i.isLt) := rfl

lemma ofChord_center (γ : Chord D a b) (hab : a.outside≠b.outside)
    (i : Fin γ.val.length) : (ofChord γ hab).center i=γ.val[i.val] := by
  rw [CenterPath.center,ofChord_point]
  simp only [Fin.val_succ,Fin.val_castSucc,extendedTrace,List.getElem_cons_succ]
  exact List.getElem_append_left i.isLt

/-- The already defined source Chord has a nonzero exact center-tensor
orientation coefficient. This identifies the finite transfer coefficient with its path contribution. -/
theorem chord_orientation_nonzero (γ : Chord D a b) (hab : a.outside≠b.outside) :
    (ofChord γ hab).orientationSum ≠ 0 :=
  (ofChord γ hab).orientationSum_ne_zero

end CriticalHoneycomb.Transfer.ChordOrientations
namespace CriticalHoneycomb.Transfer.ChordOrientations
open PhysicalTiles CenterPartition
open scoped BigOperators

lemma CenterPath.local_of_support {n : ℕ} (p : CenterPath n) (σ : Wire → Fin 3)
    (hs : ∀ w, w ∉ Set.range p.edge → σ w=1) (i : Fin n) (k : Fin 3) :
    σ (incidentWire (p.center i) k) =
      if k=p.side i.castSucc then σ (p.edge i.castSucc)
      else if k=p.side i.succ then σ (p.edge i.succ) else 1 := by
  split_ifs with hin hout
  · subst k; rw [p.in_wire]
  · subst k; rw [p.out_wire]
  · apply hs
    rw [p.incident_edge_iff]
    tauto

lemma CenterPath.factor_of_support {n : ℕ} (p : CenterPath n) (σ : Wire → Fin 3)
    (hs : ∀ w, w ∉ Set.range p.edge → σ w=1) (i : Fin n) :
    centerTensor σ (p.center i)=p.factor i (fun j=>σ (p.edge j)) := by
  change localTensor _ (fun k=>σ (incidentWire (p.center i) k))=_
  unfold CenterPath.factor
  congr 1
  funext k
  exact p.local_of_support σ hs i k

/-- Uniqueness concerns the actual full honeycomb wire assignment, not only
the ordered list of path coefficients. Vacant wires are fixed to spin one. -/
theorem CenterPath.full_orientation_unique {n : ℕ} (p : CenterPath n) (σ : Wire → Fin 3)
    (hs : ∀ w, w ∉ Set.range p.edge → σ w=1)
    (hroot : σ (p.edge 0)=outSpin (p.point 0) (p.side 0))
    (hn : ∀ i, centerTensor σ (p.center i)≠0) : σ=p.spins := by
  have he := p.orientation_unique (fun j=>σ (p.edge j)) hroot (by
    intro i
    rw [←p.factor_of_support σ hs i]
    exact hn i)
  funext w
  by_cases hw : w∈Set.range p.edge
  · obtain ⟨i,rfl⟩ := hw
    rw [p.spins_edge]
    exact congrFun he i
  · rw [hs w hw,p.spins_off w hw]

lemma CenterPath.point_cases {n : ℕ} (p : CenterPath n) (j : Fin (n+2)) :
    p.point j=p.point 0 ∨ p.point j=p.point (Fin.last (n+1)) ∨
      ∃ i : Fin n, p.point j=p.center i := by
  cases j using Fin.cases with
  | zero => exact Or.inl rfl
  | succ j =>
    cases j using Fin.lastCases with
    | last => exact Or.inr (Or.inl rfl)
    | cast i => exact Or.inr (Or.inr ⟨i,rfl⟩)

lemma CenterPath.incident_off {n : ℕ} (p : CenterPath n) (v : Center)
    (h0 : v≠p.point 0) (hl : v≠p.point (Fin.last (n+1)))
    (hv : v∉Set.range p.center) (k : Fin 3) :
    incidentWire v k ∉ Set.range p.edge := by
  rintro ⟨j,hj⟩
  obtain ⟨hk,hleft|hright⟩ := (incidentWire_eq_iff _ _ _ _).mp hj
  · rcases p.point_cases j.castSucc with he|he|⟨i,he⟩
    · exact h0 (hleft.symm.trans he)
    · exact hl (hleft.symm.trans he)
    · exact hv ⟨i,(hleft.symm.trans he).symm⟩
  · rw [p.step j] at hright
    rcases p.point_cases j.succ with he|he|⟨i,he⟩
    · exact h0 (hright.symm.trans he)
    · exact hl (hright.symm.trans he)
    · exact hv ⟨i,(hright.symm.trans he).symm⟩

lemma CenterPath.off_center_one {n : ℕ} (p : CenterPath n) (v : Center)
    (h0 : v≠p.point 0) (hl : v≠p.point (Fin.last (n+1)))
    (hv : v∉Set.range p.center) : centerTensor p.spins v=1 := by
  have hs (k : Fin 3) : p.spins (incidentWire v k)=1 :=
    p.spins_off _ (p.incident_off v h0 hl hv k)
  unfold centerTensor
  simp only [hs]
  split <;> simp [upTensor,downTensor,Planar.empty,Planar.occupied,Planar.cup]

lemma CenterPath.product_nonzero {n : ℕ} (p : CenterPath n) (D : Finset Center)
    (h0 : p.point 0∉D) (hl : p.point (Fin.last (n+1))∉D) :
    centerProduct D p.spins≠0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro v hv
  by_cases hc : v∈Set.range p.center
  · obtain ⟨i,rfl⟩ := hc
    exact p.center_nonzero i
  · rw [p.off_center_one v (fun he=>h0 (he ▸ hv)) (fun he=>hl (he ▸ hv)) hc]
    exact one_ne_zero

noncomputable def extendFiniteSpins (V : Finset Wire) (σ : V → Fin 3) : Wire → Fin 3 :=
  fun w=>if h : w∈V then σ ⟨w,h⟩ else 1

lemma extendFiniteSpins_at (V : Finset Wire) (σ : V → Fin 3) (w : V) :
    extendFiniteSpins V σ w=σ w := by simp [extendFiniteSpins]

lemma CenterPath.extend_restrict {n : ℕ} (p : CenterPath n) (V : Finset Wire)
    (he : ∀ i, p.edge i∈V) :
    extendFiniteSpins V (fun w=>p.spins w)=p.spins := by
  funext w
  unfold extendFiniteSpins
  split_ifs with hw
  · rfl
  · symm
    apply p.spins_off
    rintro ⟨i,rfl⟩
    exact hw (he i)

/-- Exact finite center contraction restricted to the occupied set of one
literal chord. Vacant wires have the actual spin one; the first boundary
arrow is fixed. No orientation coefficient has been supplied as an input. -/
noncomputable def CenterPath.finiteContraction {n : ℕ} (p : CenterPath n)
    (D : Finset Center) (V : Finset Wire) : ℂ := by
  classical
  exact ∑ σ : V → Fin 3,
    if (∀ w : V, w.val ∉ Set.range p.edge → σ w=1) ∧
       extendFiniteSpins V σ (p.edge 0)=outSpin (p.point 0) (p.side 0)
    then centerProduct D (extendFiniteSpins V σ) else 0

/-- The physical full-wire finite contraction is just its single directed
path term. This binds noncancellation to actual center products on a domain. -/
theorem CenterPath.finiteContraction_eq {n : ℕ} (p : CenterPath n)
    (D : Finset Center) (V : Finset Wire)
    (he : ∀ i, p.edge i∈V) (hc : ∀ i, p.center i∈D) :
    p.finiteContraction D V=centerProduct D p.spins := by
  classical
  unfold CenterPath.finiteContraction
  rw [Finset.sum_eq_single (fun w : V=>p.spins w)]
  · have hs : ∀ w : V, w.val ∉ Set.range p.edge → p.spins w=1 := fun w h=>p.spins_off w h
    rw [p.extend_restrict V he]
    simp only [p.spins_edge,Fin.castSucc_zero,and_true]
    exact ite_eq_left hs
  · intro σ hσ hne
    split_ifs with hbound
    · by_contra hn
      have hs : ∀ w, w∉Set.range p.edge → extendFiniteSpins V σ w=1 := by
        intro w hw
        unfold extendFiniteSpins
        split_ifs with hm
        · exact hbound.1 ⟨w,hm⟩ hw
        · rfl
      have hu := p.full_orientation_unique (extendFiniteSpins V σ) hs hbound.2 (by
        intro i
        exact (Finset.prod_ne_zero_iff.mp hn) (p.center i) (hc i))
      apply hne
      funext w
      have hh := congrFun hu w.val
      simpa only [extendFiniteSpins_at] using hh
    · rfl
  · simp

/-- Exact noncancellation of the loop-free component inside any containing
finite domain excluding its two exterior endpoints. -/
theorem CenterPath.finiteContraction_ne_zero {n : ℕ} (p : CenterPath n)
    (D : Finset Center) (V : Finset Wire)
    (he : ∀ i, p.edge i∈V) (hc : ∀ i, p.center i∈D)
    (h0 : p.point 0∉D) (hl : p.point (Fin.last (n+1))∉D) :
    p.finiteContraction D V≠0 := by
  rw [p.finiteContraction_eq D V he hc]
  exact p.product_nonzero D h0 hl

end CriticalHoneycomb.Transfer.ChordOrientations
namespace CriticalHoneycomb.Transfer.PhysicalTiles
open Planar
open scoped BigOperators

noncomputable def maskedCell (q : Shape) (w n s e : Fin 3) : ℂ := by
  classical
  exact if spinOccupied w=q.selection.west ∧ spinOccupied n=q.selection.north ∧
      spinOccupied s=q.selection.south ∧ spinOccupied e=q.selection.east then
    ∑ m : Fin 3, if spinOccupied m=q.selection.middle then
      upTensor w s m * downTensor e n m else 0 else 0

lemma maskedCell_empty (w n s e : Fin 3) :
    maskedCell .empty w n s e=(kappa:ℂ)^(Shape.visits .empty) * shapeTensor .empty w n s e := by
  fin_cases w <;> fin_cases n <;> fin_cases s <;> fin_cases e <;>
    simp [maskedCell,shapeTensor,Shape.selection,Shape.visits,spinOccupied,
      upTensor,downTensor,vacant,occupied,Planar.empty,cup,] 

lemma maskedCell_westSouth (w n s e : Fin 3) :
    maskedCell .westSouth w n s e=(kappa:ℂ)^(Shape.visits .westSouth) * shapeTensor .westSouth w n s e := by
  fin_cases w <;> fin_cases n <;> fin_cases s <;> fin_cases e <;>
    simp [maskedCell,shapeTensor,Shape.selection,Shape.visits,spinOccupied,
      upTensor,downTensor,vacant,occupied,Planar.empty,cup,] 

lemma maskedCell_northEast (w n s e : Fin 3) :
    maskedCell .northEast w n s e=(kappa:ℂ)^(Shape.visits .northEast) * shapeTensor .northEast w n s e := by
  fin_cases w <;> fin_cases n <;> fin_cases s <;> fin_cases e <;>
    simp [maskedCell,shapeTensor,Shape.selection,Shape.visits,spinOccupied,
      upTensor,downTensor,vacant,occupied,Planar.empty,cup,] 

lemma maskedCell_both (w n s e : Fin 3) :
    maskedCell .both w n s e=(kappa:ℂ)^(Shape.visits .both) * shapeTensor .both w n s e := by
  fin_cases w <;> fin_cases n <;> fin_cases s <;> fin_cases e <;>
    simp [maskedCell,shapeTensor,Shape.selection,Shape.visits,spinOccupied,
      upTensor,downTensor,occupied,Planar.empty,cup,] <;> ring 

lemma maskedCell_westNorth (w n s e : Fin 3) :
    maskedCell .westNorth w n s e=(kappa:ℂ)^(Shape.visits .westNorth) * shapeTensor .westNorth w n s e := by
  fin_cases w <;> fin_cases n <;> fin_cases s <;> fin_cases e <;>
    simp [maskedCell,shapeTensor,Shape.selection,Shape.visits,spinOccupied,
      upTensor,downTensor,occupied,Planar.empty,cup,Fin.sum_univ_three] <;> ring 

lemma maskedCell_southEast (w n s e : Fin 3) :
    maskedCell .southEast w n s e=(kappa:ℂ)^(Shape.visits .southEast) * shapeTensor .southEast w n s e := by
  fin_cases w <;> fin_cases n <;> fin_cases s <;> fin_cases e <;>
    simp [maskedCell,shapeTensor,Shape.selection,Shape.visits,spinOccupied,
      upTensor,downTensor,occupied,Planar.empty,cup,Fin.sum_univ_three] <;> ring 

lemma maskedCell_westEast (w n s e : Fin 3) :
    maskedCell .westEast w n s e=(kappa:ℂ)^(Shape.visits .westEast) * shapeTensor .westEast w n s e := by
  fin_cases w <;> fin_cases n <;> fin_cases s <;> fin_cases e <;>
    simp [maskedCell,shapeTensor,Shape.selection,Shape.visits,spinOccupied,
      upTensor,downTensor,occupied,Planar.empty,cup,Fin.sum_univ_three] <;> ring 

lemma maskedCell_northSouth (w n s e : Fin 3) :
    maskedCell .northSouth w n s e=(kappa:ℂ)^(Shape.visits .northSouth) * shapeTensor .northSouth w n s e := by
  fin_cases w <;> fin_cases n <;> fin_cases s <;> fin_cases e <;>
    simp [maskedCell,shapeTensor,Shape.selection,Shape.visits,spinOccupied,
      upTensor,downTensor,occupied,Planar.empty,cup,Fin.sum_univ_three] <;> ring_nf <;> simp [phase_ne_zero]

/-- The fixed physical occupancy term is exactly the source shape tensor,
including its two center weights and its actual middle-edge contraction. -/
theorem maskedCell_eq (q : Shape) (w n s e : Fin 3) :
    maskedCell q w n s e=(kappa:ℂ)^q.visits * shapeTensor q w n s e := by
  cases q
  · exact maskedCell_empty w n s e
  · exact maskedCell_westSouth w n s e
  · exact maskedCell_northEast w n s e
  · exact maskedCell_both w n s e
  · exact maskedCell_westNorth w n s e
  · exact maskedCell_southEast w n s e
  · exact maskedCell_westEast w n s e
  · exact maskedCell_northSouth w n s e

end CriticalHoneycomb.Transfer.PhysicalTiles

end OAI
