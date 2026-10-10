import Mathlib
import OAI.Combinatorics.HoneycombCorridor.StripWindows

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

 theorem adjacent_exists_slot (v u : Vertex) (h : adjacent v u) :
    ∃ k : Fin 3, neighbor v k = u := by
  cases v <;> cases u <;> simp only [adjacent] at h
  · rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨0,by simp [neighbor]⟩
    · exact ⟨1,by simp [neighbor]⟩
    · exact ⟨2,by simp [neighbor]⟩
  · rcases h with ⟨rfl,hl⟩ | ⟨rfl,rfl⟩ | ⟨hk,rfl⟩
    · exact ⟨0,by simp [neighbor]; omega⟩
    · exact ⟨1,by simp [neighbor]⟩
    · exact ⟨2,by simp [neighbor]; omega⟩

theorem exists_advance_of_adjacent (g : Germ) (v : Vertex) (ha : adjacent g.1 v)
    (hb : v ≠ neighbor g.1 g.2) : ∃ b : Bool, (advance g b).1 = v := by
  obtain ⟨k,hk⟩ := adjacent_exists_slot g.1 v ha
  have hkg : k ≠ g.2 := by
    intro he
    exact hb (he ▸ hk.symm)
  have ho : ∃ b : Bool, outgoingSlot g b = k := by
    obtain ⟨u,j⟩ := g
    fin_cases j <;> fin_cases k <;> simp_all [outgoingSlot]
  obtain ⟨b,hb⟩ := ho
  exact ⟨b,by simpa only [advance,hb] using hk⟩

theorem exists_word_of_chain (g : Germ) (l : List Vertex)
    (hc : (g.1 :: l).IsChain adjacent) (hn : (g.1 :: l).Nodup)
    (hp : neighbor g.1 g.2 ∉ l) :
    ∃ w : List Bool, traced g w ++ [(terminalGerm g w).1] = g.1 :: l := by
  induction l generalizing g with
  | nil => exact ⟨[],rfl⟩
  | cons v l ih =>
    obtain ⟨ha,hc⟩ := List.isChain_cons_cons.mp hc
    obtain ⟨hg,hn⟩ := List.nodup_cons.mp hn
    have hb : v ≠ neighbor g.1 g.2 := by
      intro he
      exact hp (by simp [he])
    obtain ⟨b,hb⟩ := exists_advance_of_adjacent g v ha hb
    have hg' : neighbor (advance g b).1 (advance g b).2 = g.1 := by
      simp only [advance,neighbor_neighbor]
    have hc' : ((advance g b).1 :: l).IsChain adjacent := by simpa only [hb] using hc
    have hn' : ((advance g b).1 :: l).Nodup := by simpa only [hb] using hn
    have hp' : neighbor (advance g b).1 (advance g b).2 ∉ l := by
      rw [hg']
      exact fun hm => hg (List.mem_cons_of_mem _ hm)
    obtain ⟨w,hw⟩ := ih (advance g b) hc' hn' hp'
    refine ⟨b::w,?_⟩
    simp only [traced,terminalGerm,List.cons_append,hw,hb]



def layer (vertex : Vertex) : ℤ :=
  Vertex.rec (fun _ vertical => vertical) (fun _ vertical => vertical) vertex

structure BridgePath (h : ℕ) where
  vertices : List Vertex
  distinct : vertices.Nodup
  connected : vertices.IsChain adjacent
  source : vertices.head? = some (.up 0 0)
  terminal : ∃ i : ℤ, vertices.getLast? = some (.down i ((h : ℤ) - 1))
  inStrip : ∀ v ∈ vertices, 0 ≤ layer v ∧ layer v < (h : ℤ)

noncomputable def weight {h : ℕ} (p : BridgePath h) : ℝ :=
  criticalActivity ^ p.vertices.length

noncomputable def firstLengthWeight {h : ℕ} (p : BridgePath h) : ℝ :=
  (p.vertices.length : ℝ) * weight p

noncomputable def bridgeMass (h : ℕ) : ℝ := ∑' p : BridgePath h, weight p
noncomputable def bridgeLengthMass (h : ℕ) : ℝ :=
  ∑' p : BridgePath h, firstLengthWeight p
noncomputable def bridgeMean (h : ℕ) : ℝ := bridgeLengthMass h / bridgeMass h

noncomputable def InLogCorridor {h : ℕ} (p : BridgePath h) : Prop :=
  ∀ v ∈ p.vertices, |(position v).1| ≤ (h : ℝ) * (Real.log (h : ℝ)) ^ 2

def ConfinedBridgePath (h : ℕ) := {p : BridgePath h // InLogCorridor p}

noncomputable def confinedMass (h : ℕ) : ℝ :=
  ∑' p : ConfinedBridgePath h, weight p.val
noncomputable def confinedLengthMass (h : ℕ) : ℝ :=
  ∑' p : ConfinedBridgePath h, firstLengthWeight p.val
noncomputable def confinedMean (h : ℕ) : ℝ := confinedLengthMass h / confinedMass h

def Subpower (f : ℕ → ℝ) (a : ℝ) : Prop :=
  (∀ᶠ h in Filter.atTop, 0 < f h) ∧
  Filter.Tendsto (fun h : ℕ => Real.log (f h) / Real.log (h : ℝ))
    Filter.atTop (nhds a)

def FiniteBridgeSums : Prop :=
  ∀ h : ℕ, 1 ≤ h →
    Summable (weight (h := h)) ∧ Summable (firstLengthWeight (h := h)) ∧
    Summable (fun p : BridgePath h => firstLengthWeight p / bridgeMass h) ∧
    Summable (fun p : ConfinedBridgePath h => weight p.val) ∧
    Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val) ∧
    Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val / confinedMass h)

def StripMassAndBridgeLength : Prop :=
  FiniteBridgeSums ∧
  Subpower bridgeMass (-(1 : ℝ) / 4) ∧
  Subpower bridgeLengthMass ((13 : ℝ) / 12) ∧
  Subpower bridgeMean ((4 : ℝ) / 3) ∧
  Subpower confinedMass (-(1 : ℝ) / 4) ∧
  Subpower confinedLengthMass ((13 : ℝ) / 12) ∧
  Subpower confinedMean ((4 : ℝ) / 3)



@[simp] theorem layer_boxIndex (v : Vertex) : layer v = boxIndex v 0 := by
  cases v <;> simp [layer,boxIndex]

theorem bridge_exists_word (h : ℕ) (hh : 1 ≤ h) (p : BridgePath h) :
    ∃ w : List Bool, traced bottomSource w = p.vertices ∧
      layer (terminalGerm bottomSource w).1 = (h : ℤ) := by
  obtain ⟨i,hi⟩ := p.terminal
  let u : Vertex := .up i h
  have hu : layer u = (h : ℤ) := by rfl
  have hnu : u ∉ p.vertices := by
    intro hm
    have h := (p.inStrip u hm).2
    rw [hu] at h
    omega
  have hc : (p.vertices ++ [u]).IsChain adjacent := by
    apply p.connected.append (by simp)
    intro v hv a ha
    have hv' : v = .down i ((h : ℤ)-1) := by symm; simpa only [hi,Option.mem_some_iff] using hv
    have ha' : a = u := by symm; simpa using ha
    subst v; subst a
    simp [u,adjacent]
  have hn : (p.vertices ++ [u]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨p.distinct,by simp,?_⟩
    intro v hv a ha
    have ha' : a = u := by simpa using ha
    subst a
    exact fun he => hnu (he ▸ hv)
  have hp : neighbor bottomSource.1 bottomSource.2 ∉ p.vertices ++ [u] := by
    intro hm
    simp only [List.mem_append,List.mem_singleton] at hm
    rcases hm with hm | hm
    · have hi := (p.inStrip _ hm).1
      norm_num [bottomSource,neighbor,layer,boxIndex] at hi
    · have hidx := congrArg layer hm
      change (-1 : ℤ) = (h : ℤ) at hidx
      have hheight : (1 : ℤ) ≤ h := by exact_mod_cast hh
      exact (ne_of_lt (lt_of_lt_of_le (by norm_num : (-1 : ℤ) < 1) hheight)) hidx
  obtain ⟨l,hl⟩ := List.head?_eq_some_iff.mp p.source
  have hc' : (bottomSource.1 :: (l ++ [u])).IsChain adjacent := by
    simpa only [hl,List.cons_append,bottomSource] using hc
  have hn' : (bottomSource.1 :: (l ++ [u])).Nodup := by
    simpa only [hl,List.cons_append,bottomSource] using hn
  have hp' : neighbor bottomSource.1 bottomSource.2 ∉ l ++ [u] := by
    intro hm
    apply hp
    rw [hl,List.cons_append]
    exact List.mem_cons_of_mem _ hm
  obtain ⟨w,hw⟩ := exists_word_of_chain bottomSource _ hc' hn' hp'
  have heq : traced bottomSource w ++ [(terminalGerm bottomSource w).1] = p.vertices ++ [u] := by
    simpa only [hl,List.cons_append,bottomSource] using hw
  have ht : (terminalGerm bottomSource w).1 = u := by
    have ht := congrArg List.getLast? heq
    simpa using ht
  rw [ht] at heq
  exact ⟨w,List.append_cancel_right heq,ht ▸ hu⟩

noncomputable def bridgeWord (h : ℕ) (hh : 1 ≤ h) (p : BridgePath h) : List Bool :=
  (bridge_exists_word h hh p).choose

@[simp] theorem bridgeWord_trace (h : ℕ) (hh : 1 ≤ h) (p : BridgePath h) :
    traced bottomSource (bridgeWord h hh p) = p.vertices :=
  (bridge_exists_word h hh p).choose_spec.1

theorem bridgeWord_terminal_layer (h : ℕ) (hh : 1 ≤ h) (p : BridgePath h) :
    layer (terminalGerm bottomSource (bridgeWord h hh p)).1 = (h : ℤ) :=
  (bridge_exists_word h hh p).choose_spec.2

@[simp] theorem bridgeWord_length (h : ℕ) (hh : 1 ≤ h) (p : BridgePath h) :
    (bridgeWord h hh p).length = p.vertices.length := by
  rw [← traced_length bottomSource,bridgeWord_trace]

theorem bridgeWord_injective (h : ℕ) (hh : 1 ≤ h) : Function.Injective (bridgeWord h hh) := by
  intro p q hpq
  have hv := congrArg (traced bottomSource) hpq
  simp only [bridgeWord_trace] at hv
  cases p; cases q
  cases hv
  rfl

theorem bridgeWord_mem_sourceExits (h : ℕ) (hh : 1 ≤ h) (p : BridgePath h)
    (D : Finset Vertex) (hstrip : ∀ v ∈ D, InStrip h v)
    (hp : ∀ v ∈ p.vertices, v ∈ D) : bridgeWord h hh p ∈ sourceExits D bottomSource := by
  have ht : (terminalGerm bottomSource (bridgeWord h hh p)).1 ∉ D := by
    intro hm
    have hhi := (hstrip _ hm).2
    rw [← layer_boxIndex,bridgeWord_terminal_layer] at hhi
    omega
  apply (mem_sourceExits _ _ _).mpr
  refine ⟨stopped_of_trace D bottomSource _ ?_ ?_ ht,ht⟩
  · simpa only [bridgeWord_trace] using p.distinct
  · simpa only [bridgeWord_trace] using hp

end PolynomialVacuumBridge.Corridor

end

end OAI
