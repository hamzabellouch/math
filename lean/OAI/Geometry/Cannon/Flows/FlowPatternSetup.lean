import Mathlib
import OAI.Geometry.Cannon.Flows.FlowSetup
import OAI.Geometry.Cannon.Flows.IntervalAvoidingShortRange

namespace OAI

section
section
section
noncomputable section
section
section
section
section
namespace CannonApprox

open Set Metric Filter Topology CannonNode CannonMagnification CannonPairs

variable {X Γ : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    {action : Γ → X ≃ₜ X} {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {p : ∀ n, ι n → X} {r : ℕ → ℝ}

omit [CompactSpace X] in
lemma FlowSetup.margins {T : RecordData action ι p r} {ell L CE LE : ℝ} {Q : ℕ}
    (F : FlowSetup T ell L CE LE Q) (hL : 1 ≤ L) (_hCE : 0 ≤ CE) (hLE : 0 ≤ LE) :
    2 < F.A ∧ 0 ≤ F.B ∧ 0 < F.c₀ ∧ 2*L ≤ F.c₀ ∧
      CE*(2*L) ≤ (F.cPat/2)*(F.A-2)^2 ∧
      LE*(10*F.cPat)*(F.B+1)*(F.B+2) < F.c₀ ∧ 4*(F.B+1) < F.H := by
  have hc : 0 < F.c₀ := by linarith only [F.core,hL]
  have hA : 2 < F.A := by rw [F.inner]; nlinarith only [hc,hL]
  have hB : 0 ≤ F.B := by rw [F.outer]; linarith only [hA]
  have hpat : CE*(2*L) = (F.cPat/2)*(F.A-2)^2 := by
    rw [F.pattern]
    field_simp [ne_of_gt (sub_pos.mpr hA)]
  have hm : LE*(10*F.cPat)*(F.B+1)*(F.B+2) ≤ 12*F.cPat*(F.B+2)^2*LE := by
    have hb : 0 ≤ F.B+2 := by positivity
    have hnorm : LE*(10*F.cPat)*(F.B+1)*(F.B+2) =
        (10*(F.B+1))*((F.cPat*LE)*(F.B+2)) := by ring
    rw [hnorm]
    calc
      _ ≤ (12*(F.B+2))*((F.cPat*LE)*(F.B+2)) :=
        mul_le_mul_of_nonneg_right (by linarith only [hB])
          (mul_nonneg (mul_nonneg F.pattern_pos.le hLE) hb)
      _ = _ := by ring
  exact ⟨hA,hB,hc,by linarith only [F.core],hpat.le,hm.trans_lt F.margin,
    (le_max_left _ _).trans_lt F.separation⟩

omit [CompactSpace X] in
lemma FlowSetup.center_puncture {T : RecordData action ι p r} {ell L CE LE : ℝ} {Q : ℕ}
    (F : FlowSetup T ell L CE LE Q) (hB : 0 ≤ F.B+1) (g : ℕ) (i : Fin (F.S.flow.size g)) :
    F.ε ≤ dist (F.S.center g i) T.z₀ := by
  by_contra hn
  have hi := mem_closedBall.mp (F.S.center_mem hB g i)
  apply T.z₀not (F.local_domain ?_)
  rw [mem_closedBall]
  have ht := dist_triangle T.z₀ (F.S.center g i) T.x₀
  rw [dist_comm T.z₀ (F.S.center g i)] at ht
  linarith only [ht,hi,lt_of_not_ge hn]

theorem RecordData.pattern_pair (T : RecordData action ι p r)
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ r n)
    (gi gj : Γ) (xi xj pi pj : X) (R U V A B cutoff ε : ℝ)
    (hR : 0 < R) (hV : 0 < V) (hA : 0 < A) (hB : 1 ≤ B)
    (hwide : 3*U/T.H_diameter < A) (hroom : 2*U/A ≤ ε)
    (hΩi : closedBall xi ε ⊆ T.Ω) (hΩj : closedBall xj ε ⊆ T.Ω)
    (hui : ∀ y, dist (action gi y) pi*denominator xi R y ≤ U*R)
    (huj : ∀ y, dist (action gj y) pj*denominator xj R y ≤ U*R)
    (hli : ∀ y, denominator xi R y ≤ cutoff →
      R ≤ V*dist (action gi y) pi*denominator xi R y)
    (hlj : ∀ y, denominator xj R y ≤ cutoff →
      R ≤ V*dist (action gj y) pj*denominator xj R y)
    (hsmall : B*R ≤ cutoff) (havoid : A*R < 1/(V*B)) (hfar : 2*A*R ≤ dist pi pj)
    (Pat : Bool → Set X)
    (hPati : ∀ s, (action gi).symm '' Pat s ⊆ closedBall xi (B*R))
    (hPatj : ∀ s, (action gj).symm '' Pat s ⊆ closedBall xj (B*R))
    (v₀ v₁ : Bool → X) (γ : ∀ s, Path (v₀ s) (v₁ s))
    (hγ : ∀ s, range (γ s) ⊆ Pat s)
    (κ li lj : ℝ) (hκ : 0 < κ) (hli_pos : 0 < li) (hlj_pos : 0 < lj)
    (hgap : ∀ s, κ*li ≤ T.f ((action gi).symm (v₁ s))-T.f ((action gi).symm (v₀ s)))
    (hsep : ∀ x ∈ Pat false, ∀ y ∈ Pat true,
      T.f ((action gj).symm x)+lj/4 ≤ T.f ((action gj).symm y)) :
    (min (κ/4) (1/16))*li ≤ CannonCrossEnergy.oscillation T.f
      ((action gi).symm '' closedBall pj (A*R)) ∨
    (min (κ/4) (1/16))*lj ≤ CannonCrossEnergy.oscillation T.f
      ((action gj).symm '' closedBall pi (A*R)) := by
  have hP : ∀ s z, z ∈ range (γ s) → A*R < dist z pi ∧ A*R < dist z pj := by
    intro s z hz
    exact ⟨havoid.trans_le (pattern_puncture_distance (action gi) xi pi R V B cutoff
      hR hV hB hsmall hli (Pat s) (hPati s) z (hγ s hz)),
      havoid.trans_le (pattern_puncture_distance (action gj) xj pj R V B cutoff
      hR hV hB hsmall hlj (Pat s) (hPatj s) z (hγ s hz))⟩
  have henergy (g : Γ) (K : Set X) (hK : IsCompact K) (hKΩ : (action g).symm '' K ⊆ T.Ω) :
      Tendsto (fun n => meshEnergy (p n) (r n) 2 (T.H n ∘ (action g).symm) K) atTop (𝓝 0) := by
    apply T.energy g K hK _ 2 (by norm_num)
    intro z hz
    exact ⟨(action g).symm z,hKΩ (mem_image_of_mem _ hz),(action g).apply_symm_apply z⟩
  have hh := fixed_source_pair ι p r hr hrlim hpnet T.Ω T.H T.f T.continuous T.H_continuous
    T.unit T.H_limit T.H_diameter T.H_diameter_pos T.H_level
    (action gi) (action gj) xi xj pi pj R U A ε hR hA hwide hroom hΩi hΩj hui huj hfar
    v₀ v₁ γ hP (κ*li) (lj/4) (mul_pos hκ hli_pos) (by positivity) hgap
    (fun x hx y hy => hsep x (hγ false hx) y (hγ true hy)) (henergy gi) (henergy gj)
  rcases hh with hh | hh
  · left
    calc
      _ ≤ (κ/4)*li := mul_le_mul_of_nonneg_right (min_le_left _ _) hli_pos.le
      _ = (κ*li)/4 := by ring
      _ ≤ _ := hh
  · right
    calc
      _ ≤ (1/16)*lj := mul_le_mul_of_nonneg_right (min_le_right _ _) hlj_pos.le
      _ = (lj/4)/4 := by ring
      _ ≤ _ := hh

end CannonApprox

end

section

section

section

section

section

section

section

section

section

namespace CannonCapacity

open Finset Set

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

section

open Finset

namespace CannonCapacity

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

namespace CannonCapacity

open Set Metric Finset

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

section

namespace CannonCapacity

open Set Metric Finset CannonAnnular

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

section

namespace CannonCapacity

open Set Metric Finset CannonAnnular CannonPacking

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

namespace CannonCapacity

open Set Metric Finset CannonAnnular

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

section

namespace CannonCapacity

open Set Metric Finset CannonAnnular CannonPacking

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

section

open Set Metric Finset

namespace CannonCapacity

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

namespace CannonCapacity

open Set Metric Finset CannonPacking CannonAnnular Filter Topology

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

namespace CannonCapacity

open Set Finset

attribute [local instance] Classical.propDecidable

end CannonCapacity

namespace CannonCapacity

open Set Metric Finset

attribute [local instance] Classical.propDecidable

end CannonCapacity

namespace CannonNode

open Set Metric Finset CannonCapacity CannonFlow

attribute [local instance] Classical.propDecidable

end CannonNode

namespace CannonNode

open Set Metric Finset CannonCapacity CannonFlow CannonPacking CannonAnnular Filter Topology

attribute [local instance] Classical.propDecidable

end CannonNode

end

namespace CannonNode

open Set Metric Finset Filter Topology CannonPacking CannonAnnular CannonMagnification

attribute [local instance] Classical.propDecidable

end CannonNode

end

section

section

open Set Filter Finset

namespace CannonFlow

namespace FiniteFlow

attribute [local instance] Classical.propDecidable

variable (T : FiniteFlow)

end FiniteFlow

namespace FiniteFlow

attribute [local instance] Classical.propDecidable

variable (T : FiniteFlow)

end FiniteFlow

end CannonFlow

namespace CannonFlow

open Finset

attribute [local instance] Classical.propDecidable

end CannonFlow

end

namespace CannonNode

open Set Metric Finset CannonFlow

attribute [local instance] Classical.propDecidable

end CannonNode

end

namespace CannonNode

open Set Metric Finset Filter Topology CannonPacking CannonAnnular CannonMagnification CannonFlow

attribute [local instance] Classical.propDecidable

end CannonNode

end

section

open Set Filter Finset

namespace CannonFlow

namespace FiniteFlow

attribute [local instance] Classical.propDecidable

variable (T : FiniteFlow)

end FiniteFlow

namespace FiniteFlow

attribute [local instance] Classical.propDecidable

variable (T : FiniteFlow)

end FiniteFlow

end CannonFlow

namespace CannonFlow

open Finset

attribute [local instance] Classical.propDecidable

end CannonFlow

end

section

open Set Finset MeasureTheory Filter

namespace CannonPairCost

attribute [local instance] Classical.propDecidable

end CannonPairCost

end

namespace CannonNode.SourceConstruction

open Set Metric Finset Filter Topology CannonFlow

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MetricSpace X] {f : X → ℝ} {x₀ : X}
  {ε ell c₀ A B H ρ : ℝ} {qdim n : ℕ}

variable (S : SourceConstruction f x₀ ε ell c₀ A B H ρ qdim n)

end CannonNode.SourceConstruction

namespace CannonNode.SourceConstruction

open Set Metric Finset MeasureTheory CannonFlow

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MetricSpace X] {f : X → ℝ} {x₀ : X}
  {ε ell c₀ A B H ρ : ℝ} {qdim n : ℕ}

variable (S : SourceConstruction f x₀ ε ell c₀ A B H ρ qdim n)

end CannonNode.SourceConstruction

end

namespace CannonNode

open Set Metric CannonCapacity CannonMagnification

namespace SourceConstruction

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MetricSpace X] [ProperSpace X] {f : X → ℝ} {x₀ : X}
  {ε ell c₀ A B H ρ : ℝ} {qdim n : ℕ}

variable (S : SourceConstruction f x₀ ε ell c₀ A B H ρ qdim n)

end SourceConstruction

end CannonNode

end

namespace CannonApprox

open Set Metric CannonNode CannonMagnification

variable {X Γ : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    {action : Γ → X ≃ₜ X} {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {p : ∀ n, ι n → X} {r : ℕ → ℝ}

structure FlowPatternSetup (T : RecordData action ι p r) {ell L CE LE : ℝ} {Q : ℕ}
    (F : FlowSetup T ell L CE LE Q)
    (h : ∀ g, Fin (F.S.flow.size g) → X ≃ₜ X) where
  net : Finset X
  net_nonempty : net.Nonempty
  pat : ∀ g, Fin (F.S.flow.size g) → Bool → net
  data : ∀ g i, F.S.good (F.S.state g i) →
    ∃ v₀ v₁ : Bool → X, ∃ γ : ∀ s, Path (v₀ s) (v₁ s),
      (∀ s, range (γ s) ⊆ closedBall ((pat g i s : net) : X)
        (3*F.cPat*radius ell (160*(Q+1)*F.n))) ∧
      (∀ s, F.S.κ*F.S.len g i ≤ T.f ((h g i).symm (v₁ s))-T.f ((h g i).symm (v₀ s))) ∧
      (∀ s, (h g i).symm '' closedBall ((pat g i s : net) : X)
        (3*F.cPat*radius ell (160*(Q+1)*F.n)) ⊆ closedBall (F.S.center g i) ((F.B+2)*F.S.scale g)) ∧
      ∀ z ∈ closedBall ((pat g i false : net) : X) (3*F.cPat*radius ell (160*(Q+1)*F.n)),
        ∀ w ∈ closedBall ((pat g i true : net) : X) (3*F.cPat*radius ell (160*(Q+1)*F.n)),
          T.f ((h g i).symm z)+F.S.len g i/4 ≤ T.f ((h g i).symm w)

theorem exists_flow_patterns (T : RecordData action ι p r) {ell L CE LE : ℝ} {Q : ℕ}
    (F : FlowSetup T ell L CE LE Q) (hL : 1 ≤ L) (hCE : 0 ≤ CE) (hLE : 0 ≤ LE)
    (hpaths : ∀ x u w : X, ∀ r : ℝ, 0 < r → dist u x ≤ r → dist w x ≤ r →
      JoinedIn (ball x (L*r)) u w)
    (h : ∀ g, Fin (F.S.flow.size g) → X ≃ₜ X)
    (hexp : ∀ g i, Expansion (h g i) (F.S.center g i) (F.S.scale g) CE LE) :
    Nonempty (FlowPatternSetup T F h) := by
  classical
  obtain ⟨hA,hB,hc,hcore,hcoef₁,hcoef₂,hH⟩ := F.margins hL hCE hLE
  obtain ⟨Z,_,hnet,_⟩ := CannonNet.exists_compact_net (X:=X)
    (F.cPat*radius ell (160*(Q+1)*F.n)) (mul_pos F.pattern_pos (radius_pos _ _))
  obtain ⟨z,hz,_⟩ := hnet T.x₀
  have hZ : Z.Nonempty := ⟨z,hz⟩
  let ballOf : (Bool → Z) → Bool → Set X := fun pat s =>
    closedBall (pat s : X) (3*F.cPat*radius ell (160*(Q+1)*F.n))
  let HasPattern (g : ℕ) (i : Fin (F.S.flow.size g)) (pat : Bool → Z) : Prop :=
    ∃ v₀ v₁ : Bool → X, ∃ γ : ∀ s, Path (v₀ s) (v₁ s),
      (∀ s, range (γ s) ⊆ ballOf pat s) ∧
      (∀ s, F.S.κ*F.S.len g i ≤ T.f ((h g i).symm (v₁ s))-T.f ((h g i).symm (v₀ s))) ∧
      (∀ s, (h g i).symm '' ballOf pat s ⊆ closedBall (F.S.center g i) ((F.B+2)*F.S.scale g)) ∧
      ∀ z ∈ ballOf pat false, ∀ w ∈ ballOf pat true,
        T.f ((h g i).symm z)+F.S.len g i/4 ≤ T.f ((h g i).symm w)
  have hp : ∀ g i, F.S.good (F.S.state g i) → ∃ pat, HasPattern g i pat := by
    intro g i hi
    have hexp' : Expansion (h g i) (F.S.state g i).center
        (radius ell (F.S.state g i).depth) CE LE := by
      rw [F.S.state_depth g i]
      exact hexp g i
    obtain ⟨pat,v₀,v₁,γ,hγ,hgap,hball,hsep⟩ := F.S.node_pattern (fun z : Z => (z:X))
      T.Ω T.continuous F.local_domain L CE LE F.cPat hL hCE hLE F.pattern_pos
      hA hB hcore hcoef₁ hcoef₂ F.small
      (fun x => by obtain ⟨z,hz,hd⟩ := hnet x; exact ⟨⟨z,hz⟩,hd⟩) hpaths
      (F.S.state g i) hi (h g i) hexp'
    refine ⟨pat,v₀,v₁,γ,hγ,hgap,?_,hsep⟩
    intro s y hy
    obtain ⟨w,hw,hball⟩ := hball s
    obtain ⟨v,hv,rfl⟩ := hy
    obtain ⟨u,hu,huv⟩ := hball hv
    rw [← huv,(h g i).symm_apply_apply]
    have hloc := (F.S.Yloc (F.S.state g i) w hw).2
    have hsm := mul_le_mul_of_nonneg_right F.S.pattern_small (radius_pos ell (F.S.state g i).depth).le
    have ht := dist_triangle u w (F.S.center g i)
    change dist u w < F.c₀*radius ell ((F.S.state g i).depth+160*(Q+1)*F.n) at hu
    rw [radius_add] at hu
    rw [mem_closedBall]
    rw [F.S.state_depth g i] at hu hloc hsm
    change F.c₀*radius ell (160*(Q+1)*F.n)*F.S.scale g ≤ 1*F.S.scale g at hsm
    change dist w (F.S.center g i) ≤ (F.B+1)*F.S.scale g at hloc
    change dist u w < F.c₀*(radius ell (160*(Q+1)*F.n)*F.S.scale g) at hu
    nlinarith only [ht,hu,hloc,hsm]
  let pat : ∀ g, Fin (F.S.flow.size g) → Bool → Z := fun g i =>
    if hi : F.S.good (F.S.state g i) then (hp g i hi).choose else fun _ => ⟨z,hz⟩
  refine ⟨⟨Z,hZ,pat,?_⟩⟩
  intro g i hi
  dsimp only [pat]
  rw [dite_eq_left hi]
  exact (hp g i hi).choose_spec

end CannonApprox

end

end
end
end
end
end
end

end OAI
