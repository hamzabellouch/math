import OAI.Analysis.LipschitzHilbert.Phase.AngularAmplitudeIdentity
import OAI.Analysis.LipschitzHilbert.Trees.ResidualOscillation
import OAI.Analysis.LipschitzHilbert.Trees.SourcePathProduct

namespace OAI

/-! Exact propagation of source residual packets. The same angular
transition product occurs at every shift. A packet continuing in the
path child therefore acquires a coefficient depending only on its stop
level; Abel summation applies to one fixed raw packet prefix. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

namespace AngularGrid
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem packetAmplitude_filter_split (g : AngularGrid) (packets : Finset σ)
    (slope : σ → ℝ) (stop : σ → ℕ) (base : σ → E) (transition : ℕ → ℤ → ℂ)
    (keep : σ → Prop) (level : ℕ) (cell : ℤ) :
    g.packetAmplitude packets slope stop base transition level cell =
      g.packetAmplitude (packets.filter keep) slope stop base transition level cell+
        g.packetAmplitude (packets.filter fun s => ¬keep s) slope stop base transition level cell := by
  simp only [packetAmplitude,packetSet,Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : keep q <;> simp [hq]

/-- The product of all complete block coefficients is the one common
angular transition product over their union. -/
theorem packetPathProduct_blocks (g : AngularGrid) (transition : ℕ → ℤ → ℂ)
    (level : ℕ → ℕ) (hlevel : Monotone level) (s : ℝ) {e f : ℕ} (hef : e ≤ f) :
    unaryPropagator (fun j => g.packetPathProduct transition (level j) (level (j+1)) s) e f =
      g.packetPathProduct transition (level e) (level f) s := by
  induction f, hef using Nat.le_induction with
  | base => simp [unaryPropagator,packetPathProduct]
  | succ f hef ih =>
    rw [unaryPropagator_succ_right _ hef,ih,
      ← g.packetPathProduct_split transition (hlevel hef) (hlevel (Nat.le_succ f))]

/-- A packet whose top lies in the path child has the same partial
transition coefficient as the path itself, through its stopping level. -/
theorem propagated_packet_coefficient (g : AngularGrid) (transition : ℕ → ℤ → ℂ)
    (level : ℕ → ℕ) (hlevel : Monotone level) (pathSlope packetSlope : ℝ)
    {e j stop : ℕ} (hej : e ≤ j) (hstop : level j ≤ stop) (hstop' : stop ≤ level (j+1))
    (hcell : g.index (level (j+1)) packetSlope = g.index (level (j+1)) pathSlope) :
    unaryPropagator (fun b => g.packetPathProduct transition (level b) (level (b+1)) pathSlope) e j *
      g.packetPathProduct transition (level j) stop packetSlope =
        g.packetPathProduct transition (level e) stop pathSlope := by
  rw [g.packetPathProduct_blocks transition level hlevel pathSlope hej,
    g.packetPathProduct_eq_of_cell transition (level j) stop (g.index_eq_of_le hstop' hcell),
    ← g.packetPathProduct_split transition (hlevel hej) hstop]

/-- Generic one-child recurrence. The complementary summand is the
entire amplitude of packets whose tops leave the distinguished child. -/
theorem packetAmplitude_one_child (g : AngularGrid) (packets : Finset σ)
    (slope : σ → ℝ) (stop : σ → ℕ) (base : σ → E) (transition : ℕ → ℤ → ℂ)
    (keep : σ → Prop) {lower upper : ℕ} (hlu : lower ≤ upper) (s : ℝ)
    (hkeep : ∀ q ∈ packets, keep q → g.index upper (slope q) = g.index upper s)
    (hlong : ∀ q ∈ packets, upper ≤ stop q →
      g.index upper (slope q) = g.index upper s → keep q) :
    g.packetAmplitude packets slope stop base transition lower (g.index lower s) =
      g.packetPathProduct transition lower upper s •
        g.packetAmplitude packets slope stop base transition upper (g.index upper s)+
      g.packetResidual (packets.filter keep) slope stop base transition lower upper (g.index lower s)+
      g.packetAmplitude (packets.filter fun q => ¬keep q) slope stop base transition lower
        (g.index lower s) := by
  have hupper : g.packetAmplitude (packets.filter keep) slope stop base transition upper
      (g.index upper s) = g.packetAmplitude packets slope stop base transition upper (g.index upper s) := by
    unfold packetAmplitude
    congr 1
    ext q
    simp only [packetSet,Finset.mem_filter]
    constructor
    · tauto
    · rintro ⟨hqp,hcell,hstop⟩
      exact ⟨⟨hqp,hlong q hqp hstop hcell⟩,hcell,hstop⟩
  have hblock := g.packetAmplitude_block (packets.filter keep) slope stop base transition
    hlu (g.index lower s) {g.index upper s} (fun _ => s)
    (by intro c hc; exact (Finset.mem_singleton.mp hc).symm)
    (by intro c _; rfl) (by
      intro q hq _
      have hqp := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1)
      exact Finset.mem_singleton.mpr (hkeep q hqp.1 hqp.2))
  simp only [Finset.sum_singleton,hupper] at hblock
  rw [g.packetAmplitude_filter_split packets slope stop base transition keep lower (g.index lower s),hblock]
  abel

variable {ι X : Type*}

def sourceContinuingPackets (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (packets : Finset σ) (assigned : σ → ι)
    (upper : ℕ) (pathSlope : ℝ) : Finset σ :=
  packets.filter (fun q => assigned q ∈ g.cellTops tops slope precision cutoff upper
    (g.index upper pathSlope))

/-- The recurrence uses the actual eligible-top child, not a selected
packet child or a positive-amplitude child. -/
theorem sourcePacketAmplitude_unary_recurrence (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → ι) (stop : σ → ℕ)
    (value : σ → E) (phase : ℕ → ℂ) (a : ℝ) (x : X)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (heligible : ∀ q ∈ packets, g.eligible cutoff (precision (assigned q)) (stop q))
    {lower upper : ℕ} (hlu : lower ≤ upper) (pathSlope : ℝ) :
    let keep := fun q => assigned q ∈ g.cellTops tops slope precision cutoff upper
      (g.index upper pathSlope)
    let base := g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x
    let transition := g.sourceTransition tops slope precision cutoff weight K gap phase x
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop value
      phase a x lower (g.index lower pathSlope) =
      g.packetPathProduct transition lower upper pathSlope •
        g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop value
          phase a x upper (g.index upper pathSlope)+
      g.packetResidual (packets.filter keep) (fun q => slope (assigned q)) stop base transition
        lower upper (g.index lower pathSlope)+
      g.packetAmplitude (packets.filter fun q => ¬keep q) (fun q => slope (assigned q)) stop base
        transition lower (g.index lower pathSlope) := by
  dsimp only
  have hkeep (q : σ) (_hq : q ∈ packets)
      (hq : assigned q ∈ g.cellTops tops slope precision cutoff upper (g.index upper pathSlope)) :
      g.index upper (slope (assigned q)) = g.index upper pathSlope :=
    ((g.mem_cellTops _ _ _ _ _ _ _).mp hq).2.1
  have hlong (q : σ) (hqp : q ∈ packets) (hstop : upper ≤ stop q)
      (hcell : g.index upper (slope (assigned q)) = g.index upper pathSlope) :
      assigned q ∈ g.cellTops tops slope precision cutoff upper (g.index upper pathSlope) :=
    (g.mem_cellTops _ _ _ _ _ _ _).mpr ⟨hassigned q hqp,hcell,
      g.eligible_of_le (hp _ (hassigned q hqp)) hstop (heligible q hqp)⟩
  have h := g.packetAmplitude_one_child packets (fun q => slope (assigned q)) stop
    (g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x)
    (g.sourceTransition tops slope precision cutoff weight K gap phase x)
    (fun q => assigned q ∈ g.cellTops tops slope precision cutoff upper (g.index upper pathSlope))
    hlu pathSlope hkeep hlong
  convert h using 1
  all_goals simp only [sourcePacketAmplitude,packetAmplitude,packetResidual,
    packetSet,Finset.sum_filter]
  congr 3
  all_goals
    funext q
    by_cases hq : assigned q ∈ g.cellTops tops slope precision cutoff upper (g.index upper pathSlope)
    · simp only [hq,ite_true,not_true_eq_false,ite_false]
    · simp only [hq,ite_false,not_false_eq_true,ite_true]

/-- The actual source coefficient is the common later-starting weight
whenever the packet and path share the relevant terminal cell. -/
theorem source_packet_common_weight (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (a : ℝ) (x : X) (pathTop : ι) (htop : pathTop ∈ tops) (upper : ℕ)
    (he : g.eligible cutoff (precision pathTop) upper)
    (packetTop : ι) {start stop : ℕ} (hstop : stop ≤ upper)
    (hcell : g.index upper (slope packetTop) = g.index upper (slope pathTop)) :
    let n := fun j => g.mass tops slope precision cutoff weight j (g.index j (slope pathTop)) x
    let m := fun j => g.sourceBoundaryMass tops slope precision cutoff weight K gap j
      (g.index (j+1) (slope pathTop)) x
    g.packetPathProduct (g.sourceTransition tops slope precision cutoff weight K gap phase x)
      start stop (slope packetTop)*
      ((g.mass tops slope precision cutoff weight stop (g.index stop (slope packetTop)) x^(-a) : ℝ) : ℂ) =
      segmentWeight n (boundaryLog n m) phase a start stop := by
  dsimp only
  have hn (j : ℕ) (hj : j ≤ upper) :
      0 < g.mass tops slope precision cutoff weight j (g.index j (slope pathTop)) x :=
    g.path_mass_pos tops slope precision cutoff weight hw j pathTop htop
      (g.eligible_of_le (hp pathTop htop) hj he) x
  rw [g.packetPathProduct_eq_of_cell _ start stop (g.index_eq_of_le hstop hcell),
    g.index_eq_of_le hstop hcell]
  rw [segmentWeight_eq_path_product _ _ phase a start stop (hn stop hstop)
    (fun j hj => hn (j+1) ((Nat.succ_le_of_lt (Finset.mem_Ico.mp hj).2).trans hstop))
    (fun j hj => (hn (j+1) ((Nat.succ_le_of_lt (Finset.mem_Ico.mp hj).2).trans hstop)).trans_le
      (g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
        (fun t x => (hw t x).le) hK gap j (slope pathTop) x).1)]
  simp only [packetPathProduct,sourceTransition,analyticTransition]
  ring

end AngularGrid

/-- Grouping a finite packet sum by its actual integer stopping level. -/
theorem weighted_packet_sum_by_stop {σ E : Type*} [AddCommMonoid E] [Module ℂ E]
    (packets : Finset σ) (stop : σ → ℕ) (value : σ → E) (weight : ℕ → ℂ)
    (lower upper : ℕ) :
    (∑ q ∈ packets.filter (fun q => lower ≤ stop q ∧ stop q < upper),
      weight (stop q) • value q) =
    ∑ k ∈ Finset.Ico lower upper,
      weight k • ∑ q ∈ packets.filter (fun q => stop q = k), value q := by
  classical
  let S := packets.filter (fun q => lower ≤ stop q ∧ stop q < upper)
  have hmap : ∀ q ∈ S, stop q ∈ Finset.Ico lower upper := by
    intro q hq
    exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hq).2
  rw [show packets.filter (fun q => lower ≤ stop q ∧ stop q < upper) = S from rfl,
    ← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro k hk
  have hset : S.filter (fun q => stop q = k) = packets.filter (fun q => stop q = k) := by
    ext q
    simp only [S,Finset.mem_filter]
    constructor
    · tauto
    · intro hq
      refine ⟨⟨hq.1,?_⟩,hq.2⟩
      simpa only [hq.2] using Finset.mem_Ico.mp hk
  rw [hset,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [(Finset.mem_filter.mp hq).2]

/-- Consecutive block intervals exactly fill the corresponding angular
interval, regardless of their unequal lengths. -/
theorem sum_consecutive_block_intervals {E : Type*} [AddCommMonoid E]
    (level : ℕ → ℕ) (hlevel : Monotone level) (f : ℕ → E)
    {e b : ℕ} (heb : e ≤ b) :
    (∑ j ∈ Finset.Ico e b, ∑ k ∈ Finset.Ico (level j) (level (j+1)), f k) =
      ∑ k ∈ Finset.Ico (level e) (level b), f k := by
  induction b, heb using Nat.le_induction with
  | base => simp
  | succ b heb ih =>
    rw [Finset.sum_Ico_succ_top heb,ih]
    exact Finset.sum_Ico_consecutive f (hlevel heb) (hlevel (Nat.le_succ b))

namespace AngularGrid
variable {σ ι X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Stop intervals belonging to different blocks are disjoint. -/
theorem block_of_stop_unique (level : ℕ → ℕ) (hlevel : StrictMono level)
    {i j k : ℕ} (hi : level i ≤ k ∧ k < level (i+1))
    (hj : level j ≤ k ∧ k < level (j+1)) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have h := hlevel.monotone (show i+1 ≤ j by omega)
    omega
  · have h := hlevel.monotone (show j+1 ≤ i by omega)
    omega

/-- The residual subset is fixed by the path and stopping levels. It
does not depend on the point at which the amplitude is evaluated. -/
def fixedPathResidualPackets (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (packets : Finset σ)
    (assigned : σ → ι) (stop : σ → ℕ) (level : ℕ → ℕ) (count : ℕ) (pathSlope : ℝ) : Finset σ :=
  packets.filter (fun q => ∃ j < count, (level j ≤ stop q ∧ stop q < level (j+1)) ∧
    assigned q ∈ g.cellTops tops slope precision cutoff (level (j+1))
      (g.index (level (j+1)) pathSlope))

theorem fixedPathResidualPackets_block (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (packets : Finset σ)
    (assigned : σ → ι) (stop : σ → ℕ) (level : ℕ → ℕ) (hlevel : StrictMono level)
    (count : ℕ) (pathSlope : ℝ) {j : ℕ} (hj : j < count) :
    (g.fixedPathResidualPackets tops slope precision cutoff packets assigned stop level count pathSlope).filter
      (fun q => level j ≤ stop q ∧ stop q < level (j+1)) =
    (g.sourceContinuingPackets tops slope precision cutoff packets assigned (level (j+1)) pathSlope).filter
      (fun q => level j ≤ stop q ∧ stop q < level (j+1)) := by
  ext q
  simp only [fixedPathResidualPackets,sourceContinuingPackets,Finset.mem_filter]
  constructor
  · rintro ⟨⟨hqp,k,hk,hks,hkt⟩,hjs⟩
    have heq : k = j := block_of_stop_unique level hlevel hks hjs
    subst k
    exact ⟨⟨hqp,hkt⟩,hjs⟩
  · rintro ⟨⟨hqp,hkt⟩,hjs⟩
    exact ⟨⟨hqp,j,hj,hjs,hkt⟩,hjs⟩

/-- Once a packet's top continues in the path child, its parent-cell
condition in the residual is automatic by angular-grid nesting. -/
theorem packetResidual_continuing_eq (g : AngularGrid) (packets : Finset σ)
    (slope : σ → ℝ) (stop : σ → ℕ) (base : σ → E) (transition : ℕ → ℤ → ℂ)
    (keep : σ → Prop) {lower upper : ℕ} (hlu : lower ≤ upper) (s : ℝ)
    (hkeep : ∀ q ∈ packets, keep q → g.index upper (slope q) = g.index upper s) :
    g.packetResidual (packets.filter keep) slope stop base transition lower upper (g.index lower s) =
      ∑ q ∈ (packets.filter keep).filter (fun q => lower ≤ stop q ∧ stop q < upper),
        g.packetPathProduct transition lower (stop q) (slope q) • base q := by
  unfold packetResidual
  apply Finset.sum_congr
  · ext q
    simp only [packetSet,Finset.mem_filter]
    constructor
    · tauto
    · rintro ⟨⟨hqp,hqk⟩,hlo,hhi⟩
      exact ⟨⟨⟨hqp,hqk⟩,g.index_eq_of_le hlu (hkeep q hqp hqk),hlo⟩,hhi⟩
  · intro q _
    rfl

/-- After propagation from an earlier block, the continuing residual
uses the same coefficient at each stop level. Every packet remains in
the deterministic path residual subset defined above. -/
theorem source_propagated_residual_eq (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (packets : Finset σ)
    (assigned : σ → ι) (stop : σ → ℕ) (value : σ → E) (phase : ℕ → ℂ)
    (a : ℝ) (x : X) (level : ℕ → ℕ) (hlevel : StrictMono level) (count : ℕ)
    (pathTop : ι) (htop : pathTop ∈ tops)
    {e j : ℕ} (hej : e ≤ j) (hj : j < count)
    (he : g.eligible cutoff (precision pathTop) (level (j+1))) :
    let transition := g.sourceTransition tops slope precision cutoff weight K gap phase x
    let base := g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x
    let Q := g.fixedPathResidualPackets tops slope precision cutoff packets assigned stop level count (slope pathTop)
    let n := fun k => g.mass tops slope precision cutoff weight k (g.index k (slope pathTop)) x
    let m := fun k => g.sourceBoundaryMass tops slope precision cutoff weight K gap k
      (g.index (k+1) (slope pathTop)) x
    unaryPropagator (fun b => g.packetPathProduct transition (level b) (level (b+1)) (slope pathTop)) e j •
      g.packetResidual (g.sourceContinuingPackets tops slope precision cutoff packets assigned
        (level (j+1)) (slope pathTop)) (fun q => slope (assigned q)) stop base transition
        (level j) (level (j+1)) (g.index (level j) (slope pathTop)) =
    ∑ q ∈ Q.filter (fun q => level j ≤ stop q ∧ stop q < level (j+1)),
      segmentWeight n (boundaryLog n m) phase a (level e) (stop q) • value q := by
  dsimp only
  let transition := g.sourceTransition tops slope precision cutoff weight K gap phase x
  let base := g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x
  let keep := fun q => assigned q ∈ g.cellTops tops slope precision cutoff
    (level (j+1)) (g.index (level (j+1)) (slope pathTop))
  have hkeep (q : σ) (_hq : q ∈ packets) (hk : keep q) :
      g.index (level (j+1)) (slope (assigned q)) = g.index (level (j+1)) (slope pathTop) :=
    (g.mem_cellTops _ _ _ _ _ _ _).mp hk |>.2.1
  have hres := g.packetResidual_continuing_eq packets
    (fun q => slope (assigned q)) stop base transition keep
    (hlevel.monotone (Nat.le_succ j)) (slope pathTop) hkeep
  have hset : @Finset.filter σ keep (fun q => Classical.propDecidable (keep q)) packets =
      g.sourceContinuingPackets tops slope precision cutoff packets assigned
      (level (j+1)) (slope pathTop) := by
    ext q
    simp only [Finset.mem_filter,sourceContinuingPackets,keep]
  rw [hset] at hres
  rw [hres]
  rw [← g.fixedPathResidualPackets_block tops slope precision cutoff packets assigned stop
    level hlevel count (slope pathTop) hj,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hqc : q ∈ (g.sourceContinuingPackets tops slope precision cutoff packets assigned
      (level (j+1)) (slope pathTop)).filter
      (fun q => level j ≤ stop q ∧ stop q < level (j+1)) := by
    rw [← g.fixedPathResidualPackets_block tops slope precision cutoff packets assigned stop
      level hlevel count (slope pathTop) hj]
    exact hq
  obtain ⟨hqchild,hs⟩ := Finset.mem_filter.mp hqc
  have hqpacket := (Finset.mem_filter.mp hqchild).1
  have hcell := hkeep q hqpacket (Finset.mem_filter.mp hqchild).2
  have hmcell := g.index_eq_of_le hs.2.le hcell
  have hc := g.propagated_packet_coefficient transition level hlevel.monotone
    (slope pathTop) (slope (assigned q)) hej hs.1 hs.2.le hcell
  have hwgt := g.source_packet_common_weight tops slope precision cutoff weight hp hw hK gap phase
    a x pathTop htop (level (j+1)) he pathTop hs.2.le rfl (start := level e)
  change _ • (_ • base q) = _
  simp only [base,sourcePacketBase,smul_smul]
  rw [← mul_assoc,hc,hmcell]
  exact congrArg (fun z : ℂ => z • value q) hwgt

/-- The sum of propagated residuals over consecutive blocks is one
weighted stop-level interval of the fixed raw residual family. -/
theorem source_propagated_residual_interval (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (packets : Finset σ)
    (assigned : σ → ι) (stop : σ → ℕ) (value : σ → E) (phase : ℕ → ℂ)
    (a : ℝ) (x : X) (level : ℕ → ℕ) (hlevel : StrictMono level) (count : ℕ)
    (pathTop : ι) (htop : pathTop ∈ tops)
    {e f : ℕ} (hef : e ≤ f) (hfc : f ≤ count)
    (he : g.eligible cutoff (precision pathTop) (level f)) :
    let transition := g.sourceTransition tops slope precision cutoff weight K gap phase x
    let base := g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x
    let Q := g.fixedPathResidualPackets tops slope precision cutoff packets assigned stop level count (slope pathTop)
    let n := fun k => g.mass tops slope precision cutoff weight k (g.index k (slope pathTop)) x
    let m := fun k => g.sourceBoundaryMass tops slope precision cutoff weight K gap k
      (g.index (k+1) (slope pathTop)) x
    (∑ j ∈ Finset.Ico e f,
      unaryPropagator (fun b => g.packetPathProduct transition (level b) (level (b+1)) (slope pathTop)) e j •
        g.packetResidual (g.sourceContinuingPackets tops slope precision cutoff packets assigned
          (level (j+1)) (slope pathTop)) (fun q => slope (assigned q)) stop base transition
          (level j) (level (j+1)) (g.index (level j) (slope pathTop))) =
    ∑ k ∈ Finset.Ico (level e) (level f),
      segmentWeight n (boundaryLog n m) phase a (level e) k •
        ∑ q ∈ Q.filter (fun q => stop q = k), value q := by
  dsimp only
  calc
    _ = ∑ j ∈ Finset.Ico e f, ∑ q ∈
        (g.fixedPathResidualPackets tops slope precision cutoff packets assigned stop level count (slope pathTop)).filter
          (fun q => level j ≤ stop q ∧ stop q < level (j+1)),
        segmentWeight
          (fun k => g.mass tops slope precision cutoff weight k (g.index k (slope pathTop)) x)
          (boundaryLog (fun k => g.mass tops slope precision cutoff weight k (g.index k (slope pathTop)) x)
            (fun k => g.sourceBoundaryMass tops slope precision cutoff weight K gap k (g.index (k+1) (slope pathTop)) x))
          phase a (level e) (stop q) • value q := by
      apply Finset.sum_congr rfl
      intro j hj
      exact g.source_propagated_residual_eq tops slope precision cutoff weight hp hw hK gap
        packets assigned stop value phase a x level hlevel count pathTop htop
        (Finset.mem_Ico.mp hj).1 ((Finset.mem_Ico.mp hj).2.trans_le hfc)
        (g.eligible_of_le (hp pathTop htop)
          (hlevel.monotone (Nat.succ_le_of_lt (Finset.mem_Ico.mp hj).2)) he)
    _ = ∑ j ∈ Finset.Ico e f, ∑ k ∈ Finset.Ico (level j) (level (j+1)),
        segmentWeight
          (fun k => g.mass tops slope precision cutoff weight k (g.index k (slope pathTop)) x)
          (boundaryLog (fun k => g.mass tops slope precision cutoff weight k (g.index k (slope pathTop)) x)
            (fun k => g.sourceBoundaryMass tops slope precision cutoff weight K gap k (g.index (k+1) (slope pathTop)) x))
          phase a (level e) k •
          ∑ q ∈ (g.fixedPathResidualPackets tops slope precision cutoff packets assigned stop level count (slope pathTop)).filter
            (fun q => stop q = k), value q := by
      apply Finset.sum_congr rfl
      intro j _
      exact weighted_packet_sum_by_stop _ stop value _ _ _
    _ = _ := sum_consecutive_block_intervals level hlevel.monotone _ hef

/-- Abel summation of the actual propagated residuals. All raw sums use
the one fixed residual packet subset. The coefficient cost involves
the full-root mass ratio, even for a segment starting much later. -/
theorem source_propagated_residual_bound (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (packets : Finset σ)
    (assigned : σ → ι) (stop : σ → ℕ) (value : σ → E) (phase : ℕ → ℂ)
    (a : ℝ) (x : X) (level : ℕ → ℕ) (hlevel : StrictMono level) (count : ℕ)
    (pathTop : ι) (htop : pathTop ∈ tops)
    {e f : ℕ} (hef : e < f) (hfc : f ≤ count)
    (he : g.eligible cutoff (precision pathTop) (level f)) (H : ℕ) (hH : level f ≤ H)
    {lower Z : ℝ} (ha : 0 ≤ a) (hlower : 0 < lower) (hZ : 0 ≤ Z)
    (hnlower : lower ≤ g.mass tops slope precision cutoff weight (level f)
      (g.index (level f) (slope pathTop)) x)
    (hz0 : ∀ k < level f, 0 ≤ (phase k).re) (hz : ∀ k < level f, ‖phase k‖ ≤ Z) :
    let transition := g.sourceTransition tops slope precision cutoff weight K gap phase x
    let base := g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x
    let Q := g.fixedPathResidualPackets tops slope precision cutoff packets assigned stop level count (slope pathTop)
    let n := fun k => g.mass tops slope precision cutoff weight k (g.index k (slope pathTop)) x
    let raw := fun k => ∑ q ∈ Q.filter (fun q => stop q = k), value q
    ‖∑ j ∈ Finset.Ico e f,
      unaryPropagator (fun b => g.packetPathProduct transition (level b) (level (b+1)) (slope pathTop)) e j •
        g.packetResidual (g.sourceContinuingPackets tops slope precision cutoff packets assigned
          (level (j+1)) (slope pathTop)) (fun q => slope (assigned q)) stop base transition
          (level j) (level (j+1)) (g.index (level j) (slope pathTop))‖ ≤
      lower^(-a)*(1+(a+Z*K)*Real.log (n 0/lower))*
        intervalOscillation (packetPrefix raw) H (level e) (level f) := by
  dsimp only
  rw [g.source_propagated_residual_interval tops slope precision cutoff weight hp hw hK gap
    packets assigned stop value phase a x level hlevel count pathTop htop hef.le hfc he]
  let n := fun k => g.mass tops slope precision cutoff weight k (g.index k (slope pathTop)) x
  let m := fun k => g.sourceBoundaryMass tops slope precision cutoff weight K gap k
    (g.index (k+1) (slope pathTop)) x
  let Q := g.fixedPathResidualPackets tops slope precision cutoff packets assigned stop level count (slope pathTop)
  let raw := fun k => ∑ q ∈ Q.filter (fun q => stop q = k), value q
  have hnf : lower ≤ n (level f) := hnlower
  have hanti : Antitone n := g.path_mass_antitone tops slope precision cutoff weight hp
    (fun t x => (hw t x).le) pathTop x
  have hf0 : 0 < level f := (Nat.zero_le (level e)).trans_lt (hlevel hef)
  have hlast : level f-1+1 = level f := by omega
  have hn (j : ℕ) (hj : j ≤ level f-1) : lower ≤ n j :=
    hnf.trans (hanti (by omega))
  have hm (j : ℕ) (_hj : j < level f-1) : n (j+1) ≤ m j ∧ m j ≤ n (j+1-K) :=
    g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp (fun t x => (hw t x).le)
      hK gap j (slope pathTop) x
  have hab := boundary_segment_amplitude_le_oscillation n m phase raw
    (level e) (level f-1) K H (level e) (level f) a lower Z
    (by have := hlevel hef; omega) le_rfl (by omega) hH ha hlower hZ hn
    (hanti.antitoneOn _) hm (fun k hk => hz0 k (by omega)) (fun k hk => hz k (by omega))
  rw [hlast] at hab
  apply hab.trans
  apply mul_le_mul_of_nonneg_right _ (intervalOscillation_nonneg ..)
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hlower.le _)
  apply add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (by positivity : 0 ≤ a+Z*K))
  · have hn0 : 0 < n 0 := hlower.trans_le (hn 0 (Nat.zero_le _))
    exact Real.log_le_log (div_pos hn0 (hlower.trans_le (hn _ le_rfl)))
      (div_le_div_of_nonneg_left hn0.le hlower (hn _ le_rfl))

/-- Whole amplitudes of the tops leaving the path child. Packet
coefficients still use the original full family of angular masses. -/
theorem source_offchild_top_fibers (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (K : ℕ) (gap : ℕ → ℝ)
    (bands : Finset σ) (stop : ι → σ → ℕ) (value : ι → σ → E)
    (he : ∀ t ∈ tops, ∀ k ∈ bands, g.eligible cutoff (precision t) (stop t k))
    (phase : ℕ → ℂ) (a : ℝ) (x : X) (lower upper : ℕ) (pathSlope : ℝ) :
    let child := g.cellTops tops slope precision cutoff upper (g.index upper pathSlope)
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      ((tops ×ˢ bands).filter fun q => q.1 ∉ child) Prod.fst
      (fun q => stop q.1 q.2) (fun q => value q.1 q.2) phase a x lower (g.index lower pathSlope) =
    ∑ t ∈ (g.cellTops tops slope precision cutoff lower (g.index lower pathSlope)).filter
      (fun t => t ∉ child),
      g.sourcePacketAmplitude tops slope precision cutoff weight K gap bands
        (fun _ => t) (stop t) (value t) phase a x lower (g.index lower (slope t)) := by
  dsimp only
  generalize hchilddef : g.cellTops tops slope precision cutoff upper
    (g.index upper pathSlope) = child
  simp only [sourcePacketAmplitude,packetAmplitude,packetSet,Finset.sum_filter,
    Finset.sum_product,cellTops,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hchild : t ∈ child
  · simp [hchild]
  · by_cases hcell : g.index lower (slope t) = g.index lower pathSlope
    · by_cases hel : g.eligible cutoff (precision t) lower
      · simp [hchild,hcell,hel,sourcePacketBase]
      · have hnone (k : σ) (hk : k ∈ bands) : ¬lower ≤ stop t k := by
          intro hle
          exact hel (g.eligible_of_le (hp t ht) hle (he t ht k hk))
        simp only [hchild,not_false_eq_true,hcell,hel,and_false,ite_false]
        apply Finset.sum_eq_zero
        intro k hk
        simp [hnone k hk]
    · simp [hchild,hcell]

/-- The discarded-top contribution is paid by its total removed mass,
not by the number of removed tops. -/
theorem source_offchild_amplitude_bound (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (K : ℕ) (gap : ℕ → ℝ) (bands : Finset σ) (stop : ι → σ → ℕ) (value : ι → σ → E)
    (he : ∀ t ∈ tops, ∀ k ∈ bands, g.eligible cutoff (precision t) (stop t k))
    (phase : ℕ → ℂ) (a : ℝ) (x : X) {lower upper : ℕ} (hlu : lower ≤ upper)
    (pathSlope ε : ℝ)
    (hsmall : ∀ t ∈ g.cellTops tops slope precision cutoff lower (g.index lower pathSlope),
      t ∉ g.cellTops tops slope precision cutoff upper (g.index upper pathSlope) →
      ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap bands
        (fun _ => t) (stop t) (value t) phase a x lower (g.index lower (slope t))‖ ≤ ε*weight t x) :
    let child := g.cellTops tops slope precision cutoff upper (g.index upper pathSlope)
    ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      ((tops ×ˢ bands).filter fun q => q.1 ∉ child) Prod.fst
      (fun q => stop q.1 q.2) (fun q => value q.1 q.2) phase a x lower (g.index lower pathSlope)‖ ≤
    ε*(g.mass tops slope precision cutoff weight lower (g.index lower pathSlope) x-
      g.mass tops slope precision cutoff weight upper (g.index upper pathSlope) x) := by
  dsimp only
  rw [g.source_offchild_top_fibers tops slope precision cutoff weight hp K gap bands stop value
    he phase a x lower upper pathSlope]
  let parent := g.cellTops tops slope precision cutoff lower (g.index lower pathSlope)
  let child := g.cellTops tops slope precision cutoff upper (g.index upper pathSlope)
  have hsubset : child ⊆ parent :=
    g.cellTops_subset_ancestor tops slope precision cutoff hp hlu pathSlope
  have hfilter : parent.filter (fun t => t ∈ child) = child := by
    ext t
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hsubset h,h⟩⟩
  have hpartition := Finset.sum_filter_add_sum_filter_not parent (fun t => t ∈ child)
    (fun t => weight t x)
  rw [hfilter] at hpartition
  calc
    _ ≤ ∑ t ∈ parent.filter (fun t => t ∉ child),
        ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap bands
          (fun _ => t) (stop t) (value t) phase a x lower (g.index lower (slope t))‖ := norm_sum_le _ _
    _ ≤ ∑ t ∈ parent.filter (fun t => t ∉ child), ε*weight t x :=
      Finset.sum_le_sum (fun t ht => hsmall t (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp ht).2)
    _ = ε*((∑ t ∈ parent,weight t x)-(∑ t ∈ child,weight t x)) := by
      rw [← Finset.mul_sum]
      congr 1
      linarith
    _ = _ := rfl

end AngularGrid
end LipschitzHilbert

end

end OAI
