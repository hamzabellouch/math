import OAI.Analysis.LipschitzHilbert.Estimates.NarrowWindowNeighborhood

namespace OAI

/-! A finite smooth partition over any compact set avoiding zero. Every
piece is absorbed by a positive dilation of the fixed narrow cutoff. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

abbrev NarrowWindow := ℝ × SchwartzMap ℝ ℂ

def narrowPartition : List NarrowWindow → List NarrowWindow
  | [] => []
  | b::bs => b :: (narrowPartition bs).map (fun q =>
      (q.1,q.2-lineSchwartzProduct b.2 q.2))

private theorem sum_sub_mul (b : ℂ) (l : List ℂ) :
    (l.map (fun z => z-b*z)).sum=(1-b)*l.sum := by
  induction l with
  | nil => simp
  | cons z zs ih => simp only [List.map_cons,List.sum_cons,ih]; ring

theorem narrowPartition_sum_cons (b : NarrowWindow) (bs : List NarrowWindow) (x : ℝ) :
    ((narrowPartition (b::bs)).map (fun q => q.2 x)).sum=
      b.2 x+(1-b.2 x)*((narrowPartition bs).map (fun q => q.2 x)).sum := by
  simp only [narrowPartition,List.map_cons,List.sum_cons,List.map_map,Function.comp_def,
    sub_apply,lineSchwartzProduct_apply]
  have h := sum_sub_mul (b.2 x) ((narrowPartition bs).map (fun q => q.2 x))
  simp only [List.map_map,Function.comp_def] at h
  exact congrArg (fun z : ℂ => b.2 x+z) h

theorem narrowPartition_sum_of_one (l : List NarrowWindow) (x : ℝ)
    (h : ∃ b∈l, b.2 x=1) :
    ((narrowPartition l).map (fun q => q.2 x)).sum=1 := by
  induction l with
  | nil => simp at h
  | cons b bs ih =>
    rw [narrowPartition_sum_cons]
    rcases h with ⟨q,hq,hval⟩
    rcases List.mem_cons.mp hq with rfl|hq
    · rw [hval]; ring
    · rw [ih ⟨q,hq,hval⟩]; ring

theorem narrowPartition_absorb (l : List NarrowWindow)
    (h : ∀ b∈l, 0<b.1 ∧ ∀ x, narrowBandProfile (b.1*x)*b.2 x=b.2 x) :
    ∀ q∈narrowPartition l, 0<q.1 ∧ ∀ x, narrowBandProfile (q.1*x)*q.2 x=q.2 x := by
  induction l with
  | nil => simp [narrowPartition]
  | cons b bs ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl|hq
    · exact h q (List.mem_cons_self)
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
      have hp' := ih (fun a ha => h a (List.mem_cons_of_mem _ ha)) p hp
      refine ⟨hp'.1,fun x => ?_⟩
      simp only [sub_apply,lineSchwartzProduct_apply]
      calc
        _ = narrowBandProfile (p.1*x)*p.2 x-
          b.2 x*(narrowBandProfile (p.1*x)*p.2 x) := by ring
        _ = _ := by rw [hp'.2]

theorem exists_finite_narrow_partition (K : Set ℝ) (hK : IsCompact K)
    (hzero : ∀ x∈K, x≠0) :
    ∃ l : List NarrowWindow,
      (∀ q∈l, 0<q.1 ∧ ∀ x, narrowBandProfile (q.1*x)*q.2 x=q.2 x) ∧
      ∀ x∈K, (l.map (fun q => q.2 x)).sum=1 := by
  classical
  have hex (x : K) := exists_narrow_window x.1 (hzero x.1 x.2)
  choose w hw b hb using hex
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover
    (fun x : K => Metric.ball x.1 (b x).rIn) (fun _ => Metric.isOpen_ball) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x,hx⟩,Metric.mem_ball_self (b ⟨x,hx⟩).rIn_pos⟩)
  let original : List NarrowWindow := s.toList.map (fun x =>
    (w x,((b x).hasCompactSupport.toSchwartzMap (b x).contDiff).postcompCLM
      Complex.ofRealCLM))
  refine ⟨narrowPartition original,narrowPartition_absorb original ?_,?_⟩
  · intro q hq
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hq
    exact ⟨hw x,hb x⟩
  · intro x hx
    apply narrowPartition_sum_of_one
    obtain ⟨y,hy,hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
    refine ⟨_,List.mem_map.mpr ⟨y,Finset.mem_toList.mpr hy,rfl⟩,?_⟩
    change ((b y) x:ℂ)=1
    rw [(b y).one_of_mem_closedBall (Metric.ball_subset_closedBall hxy)]
    exact Complex.ofReal_one

end LipschitzHilbert.PacketRepresentation

end

end OAI
