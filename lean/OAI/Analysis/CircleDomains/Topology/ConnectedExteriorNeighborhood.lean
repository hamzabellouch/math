import OAI.Analysis.CircleDomains.Transfer.FiniteChartConnectivity
import Mathlib.Topology.Connected.LocallyPathConnected

namespace OAI

/-! Compact nonseparating plane sets admit arbitrarily small open
neighborhoods with connected unbounded complements. The exterior is
constructed by attaching finitely many compact paths and closed balls to
an existing exterior. -/
open Set Metric Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_closed_connected_enlargement
    {W A E : Set ℂ} (hW : IsOpen W) (hWc : IsConnected W)
    (hA : IsCompact A) (hAW : A ⊆ W)
    (hE : IsClosed E) (hEc : IsConnected E) (hEW : E ⊆ W) :
    ∃ F : Set ℂ, IsClosed F ∧ IsConnected F ∧ A ∪ E ⊆ F ∧ F ⊆ W := by
  classical
  obtain ⟨p,hp⟩ := hEc.nonempty
  have hpath : IsPathConnected W := hW.isConnected_iff_isPathConnected.mp hWc
  have hlocal (x : A) : ∃ (r : ℝ) (C : Set ℂ), 0 < r ∧
      IsCompact C ∧ IsConnected C ∧ p ∈ C ∧ C ⊆ W ∧ ball x.val r ⊆ C := by
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hW x.val (hAW x.property)
    let γ := (hpath.joinedIn p (hEW hp) x.val (hAW x.property)).somePath
    have hγ : range γ ⊆ W := by
      rintro _ ⟨t,rfl⟩
      exact (hpath.joinedIn p (hEW hp) x.val (hAW x.property)).somePath_mem t
    have hcb : closedBall x.val (r/2) ⊆ W :=
      (closedBall_subset_ball (by linarith)).trans hball
    refine ⟨r/2, range γ ∪ closedBall x.val (r/2), by positivity,
      (isCompact_range γ.continuous).union (isCompact_closedBall _ _), ?_, ?_,
      union_subset hγ hcb, subset_union_of_subset_right ball_subset_closedBall _⟩
    · exact (isConnected_range γ.continuous).union
        ⟨x.val, γ.target_mem_range, mem_closedBall_self (by positivity)⟩
        (isConnected_closedBall (by positivity))
    · exact Or.inl γ.source_mem_range
  choose r C hr hCc hCconn hpC hCW hballC using hlocal
  have hcover : A ⊆ ⋃ x : A, ball x.val (r x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩, mem_ball_self (hr ⟨x,hx⟩)⟩
  obtain ⟨t,ht⟩ := hA.elim_finite_subcover (fun x : A => ball x.val (r x))
    (fun _ => isOpen_ball) hcover
  have hconn (s : Finset A) : IsConnected (E ∪ ⋃ x ∈ s, C x) := by
    induction s using Finset.induction_on with
    | empty => simpa using hEc
    | @insert x s hxs ih =>
      have h := ih.union ⟨p, Or.inl hp, hpC x⟩ (hCconn x)
      simpa only [Finset.mem_insert, iUnion_iUnion_eq_or_left, union_assoc,
        union_left_comm, union_comm] using h
  refine ⟨E ∪ ⋃ x ∈ t, C x,
    hE.union (isClosed_biUnion_finset fun x _ => (hCc x).isClosed), hconn t, ?_, ?_⟩
  · rintro x (hx | hx)
    · obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (ht hx)
      exact Or.inr (mem_iUnion₂.mpr ⟨y,hy,hballC y hxy⟩)
    · exact Or.inl hx
  · exact union_subset hEW (iUnion₂_subset fun x _ => hCW x)

lemma exists_open_connected_exterior_neighborhood
    {K U : Set ℂ} (hK : IsCompact K) (hKc : IsConnected Kᶜ)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ V : Set ℂ, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
      IsConnected Vᶜ ∧ ¬ Bornology.IsBounded Vᶜ := by
  obtain ⟨R,hR,hbound⟩ := hK.isBounded.exists_pos_norm_lt
  let E : Set ℂ := closure ((closedBall (0 : ℂ) R)ᶜ)
  have hEc : IsConnected E := (isConnected_complex_exterior_closedBall hR.le).closure
  -- A direct closed exterior contains the open exterior and still misses K.
  have hEW' : E ⊆ (ball (0 : ℂ) R)ᶜ := by
    apply closure_minimal
    · exact compl_subset_compl.mpr ball_subset_closedBall
    · exact isOpen_ball.isClosed_compl
  have hEK : E ⊆ Kᶜ := by
    intro z hz hzK
    exact hEW' hz (mem_ball_zero_iff.mpr (hbound z hzK))
  let A := closedBall (0 : ℂ) R ∩ Uᶜ
  have hA : IsCompact A := (isCompact_closedBall _ _).inter_right hU.isClosed_compl
  have hAW : A ⊆ Kᶜ := fun _ hz hzK => hz.2 (hKU hzK)
  obtain ⟨F,hF,hFc,hAF,hFW⟩ := exists_closed_connected_enlargement
    hK.isClosed.isOpen_compl hKc hA hAW isClosed_closure hEc hEK
  refine ⟨Fᶜ,hF.isOpen_compl,?_,?_,by simpa using hFc,?_⟩
  · intro z hz hzF
    exact hFW hzF hz
  · intro z hz
    by_contra hzU
    by_cases hb : z ∈ closedBall (0 : ℂ) R
    · exact hz (hAF (Or.inl ⟨hb,hzU⟩))
    · exact hz (hAF (Or.inr (subset_closure hb)))
  · simp only [compl_compl]
    intro hb
    have hbE : Bornology.IsBounded ((closedBall (0 : ℂ) R)ᶜ) :=
      hb.subset (subset_closure.trans (fun _ hz => hAF (Or.inr hz)))
    have htotal := (isBounded_closedBall (x := (0 : ℂ)) (r := R)).union hbE
    rw [union_compl_self] at htotal
    exact NormedSpace.unbounded_univ ℝ ℂ htotal

end CircleDomainRigidity

end

end OAI
