import OAI.Geometry.PlaneColoring.PaletteTransport

namespace OAI

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
def BinaryCenter (x : ℂ) (i j : Fin k) : Prop :=
  ∀ᵐ t ∂angularMeasure, t ∈ paletteSet c hc x i ∨ t ∈ paletteSet c hc x j
lemma binary_alternation (hw : WeakColoring k c) {x : ℂ} {i j : Fin k}
    (hb : BinaryCenter c hc x i j) :
    ∀ᵐ t ∂angularMeasure, (t+(sixty : Angles) ∈ paletteSet c hc x i ↔ t ∉ paletteSet c hc x i) ∧
      (t ∈ paletteSet c hc x j ↔ t ∉ paletteSet c hc x i) := by
  have hb' := (measurePreserving_add_right angularMeasure (sixty : Angles)).quasiMeasurePreserving.ae hb
  filter_upwards [hb,hb',palette_sixty c hc hw x i,palette_sixty c hc hw x j] with t h h' hi hj
  constructor
  · constructor
    · exact fun ht ht' => hi ht' ht
    · intro hnot
      exact h'.resolve_right (hj (h.resolve_left hnot))
  · constructor
    · intro ht ht'
      rcases h' with hpi | hpj
      · exact hi ht' hpi
      · exact hj ht hpj
    · exact h.resolve_left
lemma binary_pair_distinct (hw : WeakColoring k c) {x : ℂ} {i j : Fin k}
    (hb : BinaryCenter c hc x i j) : i ≠ j := by
  intro hij
  subst j
  have h := binary_alternation c hc hw hb
  have hf : ∀ᵐ t ∂angularMeasure, False := by
    filter_upwards [h,hb] with t ht hb
    have hp := hb.elim id id
    exact (ht.2.mp hp) hp
  exact hf.exists.choose_spec
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma binary_cover_real {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) {x : ℂ} {i j : Fin k}
    (hb : BinaryCenter c hc x i j) :
    ∀ᵐ t : ℝ ∂volume, t ∈ liftPalette c hc x i ∨ t ∈ liftPalette c hc x j :=
  angleMk_quasiMeasurePreserving.ae hb
lemma binary_alternation_real {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (hw : WeakColoring k c)
    {x : ℂ} {i j : Fin k} (hb : BinaryCenter c hc x i j) (φ : ℝ) :
    ∀ᵐ t : ℝ ∂volume, t+Real.pi/3+φ ∈ liftPalette c hc x i ↔ t+φ ∉ liftPalette c hc x i := by
  have h := angleMk_quasiMeasurePreserving.ae (binary_alternation c hc hw hb)
  have h' := (measurePreserving_add_right volume φ).quasiMeasurePreserving.ae h
  filter_upwards [h'] with t ht
  simpa only [liftPalette,mem_preimage,sixty,← AddCircle.coe_add,show t+φ+Real.pi/3=t+Real.pi/3+φ by ring] using ht.1
lemma alternating_twostep {A : Set ℝ} {κ : ℝ}
    (h : ∀ᵐ t : ℝ ∂volume, t+κ ∈ A ↔ t ∉ A) :
    ∀ᵐ t : ℝ ∂volume, t+2*κ ∈ A ↔ t ∈ A := by
  have h' := (measurePreserving_add_right volume κ).quasiMeasurePreserving.ae h
  filter_upwards [h,h'] with t ht ht'
  rw [show t+κ+κ=t+2*κ by ring] at ht'
  exact ht'.trans (not_congr ht) |>.trans not_not
lemma liftPalette_shift_periodic {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (x : ℂ) (i : Fin k)
    (φ : ℝ) (n : ℤ) (t : ℝ) :
    t+(n : ℝ)*(2*Real.pi)+φ ∈ liftPalette c hc x i ↔ t+φ ∈ liftPalette c hc x i := by
  have he : ((t+(n : ℝ)*(2*Real.pi)+φ : ℝ) : Angles)=((t+φ : ℝ) : Angles) := by
    rw [show t+(n : ℝ)*(2*Real.pi)+φ=t+φ+n • (2*Real.pi) by rw [zsmul_eq_mul]; ring,
      AddCircle.coe_add,AddCircle.coe_zsmul,AddCircle.coe_period,smul_zero,add_zero]
  change ((t+(n : ℝ)*(2*Real.pi)+φ : ℝ) : Angles) ∈ paletteSet c hc x i ↔ ((t+φ : ℝ) : Angles) ∈ paletteSet c hc x i
  rw [he]
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma binary_transport_invariant {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (hw : WeakColoring k c)
    {x z : ℂ} {i j : Fin k} (hb : BinaryCenter c hc x i j) (hz : BinaryCenter c hc z i j)
    {d φ : ℝ} (hd : |d|<1/2) (hD : ∀ t, (1/2 : ℝ) ≤ 1+d*binaryB d t)
    (hxr : (z-x).re=d*Real.cos φ) (hxi : (z-x).im=d*Real.sin φ) :
    ∀ᵐ t : ℝ ∂volume, t+φ ∈ liftPalette c hc x i ↔ binaryCircleMap d t+φ ∈ liftPalette c hc x i := by
  have ha : ∀ r, HasDerivAt (fun t => binaryTarget d t+φ) (1+d*binaryB d (-r)) r :=
    fun r => (binaryTarget_hasDeriv hd r).add_const φ
  have hs : ∀ r, HasDerivAt (fun t : ℝ => t+φ) 1 r := fun r => (hasDerivAt_id r).add_const φ
  have ht : ∀ r, HasDerivAt (fun t => binaryOther d t+φ) (1+d*binaryB d r) r :=
    fun r => (binaryOther_hasDeriv hd r).add_const φ
  have hn : ∀ r, Real.sin ((binaryOther d r+φ)-(r+φ))≠0 := by
    intro r
    simpa only [add_sub_add_right_eq_sub] using binary_nonparallel hd r
  have hn' : ∀ r, Real.sin ((r+φ)-(binaryOther d r+φ))≠0 := by
    intro r
    rw [show (r+φ)-(binaryOther d r+φ)=-((binaryOther d r+φ)-(r+φ)) by ring,Real.sin_neg,neg_ne_zero]
    exact hn r
  have he := binary_geometry_rotated hd hxr hxi
  have he' : ∀ r, circleTarget (samplingParameter x z 1,binaryTarget d r+φ)=
      circleSum 1 (binaryOther d r+φ,r+φ) := by
    intro r
    rw [he r]
    simp only [circleSum,Prod.mk.injEq]
    constructor <;> ring
  have hp (l : Fin k) := palette_transport_param c hc hw ha (fun r => hD (-r)) hs ht
    (fun _ => one_ne_zero) hn he l
  have hp' (l : Fin k) := palette_transport_param c hc hw ha (fun r => hD (-r)) ht hs
    (fun r => ne_of_gt (lt_of_lt_of_le (by norm_num) (hD r))) hn' he' l
  have hpat := (deriv_lower_qmp ha (fun r => hD (-r))).ae (binary_cover_real c hc hz)
  have hpx := (measurePreserving_add_right volume φ).quasiMeasurePreserving.ae (binary_cover_real c hc hb)
  have hpx' := (deriv_lower_qmp ht hD).ae (binary_cover_real c hc hb)
  have hsame : ∀ᵐ t : ℝ ∂volume, t+φ ∈ liftPalette c hc x i ↔ binaryOther d t+φ ∈ liftPalette c hc x i := by
    filter_upwards [hpat,hpx,hpx',hp i,hp j,hp' i,hp' j] with t hy hx hx' hii hjj hi' hj'
    rcases hy with hy|hy
    · exact ⟨fun hx => False.elim (hii hy hx),fun hx => False.elim (hi' hy hx)⟩
    · exact ⟨fun _ => hx'.resolve_right (hj' hy),fun _ => hx.resolve_right (hjj hy)⟩
  let A : Set ℝ := {t | t+φ ∈ liftPalette c hc x i}
  have hA : ∀ᵐ t : ℝ ∂volume, t+Real.pi/3 ∈ A ↔ t ∉ A := binary_alternation_real c hc hw hb φ
  have hp2 := (deriv_lower_qmp (binaryCircleMap_hasDeriv_t hd) hD).ae (alternating_twostep hA)
  filter_upwards [hsame,hp2] with t ht hp2
  exact ht.trans hp2
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma binary_centers_separated {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (hw : WeakColoring k c) :
    ∃ δ > 0, ∀ (x z : ℂ) (i j : Fin k), BinaryCenter c hc x i j → BinaryCenter c hc z i j →
      x ≠ z → δ ≤ dist x z := by
  obtain ⟨δ₁,hδ₁,hctrl⟩ := binary_dynamics_controls
  obtain ⟨δ₂,hδ₂,hfalse⟩ := binary_alternating_invariant_false
  refine ⟨min δ₁ δ₂,lt_min hδ₁ hδ₂,?_⟩
  intro x z i j hx hz hne
  by_contra! hdδ
  let d := ‖z-x‖
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
  have hdδ' : d < min δ₁ δ₂ := by simpa only [d,dist_eq_norm,norm_sub_rev] using hdδ
  obtain ⟨C,L,hC,hL,hB,hlo,hhi,hLip,hlarge,hadvance,hdispl,hKL,hda⟩ :=
    hctrl d hd (lt_min_iff.mp hdδ').1
  let φ := Complex.arg (z-x)
  let A : Set ℝ := {t | t+φ ∈ liftPalette c hc x i}
  apply hfalse d hd (lt_min_iff.mp hdδ').2 A
  · exact (liftPalette_measurable c hc x i).preimage (measurable_id.add_const φ)
  · exact liftPalette_shift_periodic c hc x i φ
  · exact binary_alternation_real c hc hw hx φ
  · apply binary_transport_invariant c hc hw hx hz (by rwa [abs_of_pos hd])
    · intro t
      simpa only [Nat.cast_zero,zero_mul,add_zero] using hlo 0 t
    · exact (Complex.norm_mul_cos_arg (z-x)).symm
    · exact (Complex.norm_mul_sin_arg (z-x)).symm
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
namespace EuclideanFiveColor
instance anglesNontrivial : Nontrivial Angles := by
  have : Nontrivial Circle := ⟨⟨1,-1,by
    intro h
    have hh := congrArg (fun z : Circle => (z : ℂ)) h
    norm_num at hh⟩⟩
  exact AddCircle.homeomorphCircle'.toEquiv.nontrivial
instance angularMeasure_nullSingleton : NullSingletonClass angularMeasure := by
  exact Measure.IsAddHaarMeasure.nullSingletonClass angularMeasure
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma binary_centers_countable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (hw : WeakColoring k c)
    (i j : Fin k) : {x | BinaryCenter c hc x i j}.Countable := by
  obtain ⟨δ,hδ,hsep⟩ := binary_centers_separated c hc hw
  have hp : {x | BinaryCenter c hc x i j}.PairwiseDisjoint (fun x => Metric.ball x (δ/2)) := by
    intro x hx z hz hne
    change Disjoint (Metric.ball x (δ/2)) (Metric.ball z (δ/2))
    rw [Set.disjoint_left]
    intro w hwx hwz
    have := dist_triangle x w z
    have hxw : dist x w < δ/2 := by simpa only [Metric.mem_ball,dist_comm] using hwx
    have hwz' : dist w z < δ/2 := hwz
    have := hsep x z i j hx hz hne
    linarith
  exact hp.countable_of_isOpen (fun _ _ => Metric.isOpen_ball)
    (fun x _ => ⟨x,Metric.mem_ball_self (by linarith)⟩)
lemma ae_not_binary_circle {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (hw : WeakColoring k c)
    (x : ℂ) (i j : Fin k) : ∀ᵐ t ∂angularMeasure, ¬ BinaryCenter c hc (x+direction t) i j := by
  have hi : Function.Injective (fun t => x+direction t) := by
    intro a b hab
    exact AddCircle.injective_toCircle (by positivity : (2*Real.pi:ℝ)≠0)
      (Subtype.ext (add_left_cancel hab))
  have hn := ((binary_centers_countable c hc hw i j).preimage hi).measure_zero angularMeasure
  exact (measure_eq_zero_iff_ae_notMem).mp hn
lemma exact_sample_isTrace {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) {y : ℂ}
    (hy : TypicalSampling c y 1) : IsTrace c hc y (sampleCode c hc y 1) :=
  subset_closure ⟨hy,rfl⟩
lemma trace_positive_le_palette {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) {y : ℂ}
    {b : TraceVector k} (hb : IsTrace c hc y b) (i : Fin k) :
    ∀ᵐ t ∂angularMeasure, 0 < traceValue b i t → t ∈ paletteSet c hc y i :=
  tracePositive_le_palette c hc y i ⟨b,hb⟩
lemma trace_sample_ae {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (y : ℂ) (i : Fin k) :
    traceValue (sampleCode c hc y 1) i =ᵐ[angularMeasure] sampleFn c y 1 i := by
  rw [traceValue_sampleCode]
  exact sample_ae c hc y 1 i
lemma exact_sample_palette_fixed {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) {y : ℂ}
    (hy : TypicalSampling c y 1) (i : Fin k) :
    ∀ᵐ t ∂angularMeasure, c (y+direction t)=i → t ∈ paletteSet c hc y i := by
  have hp := trace_positive_le_palette c hc (exact_sample_isTrace c hc hy) i
  have hs := trace_sample_ae c hc y i
  apply (hp.and hs).mono
  intro t ht hcolor
  apply ht.1
  rw [ht.2]
  change 0 < if c (y+(1:ℂ)*direction t)=i then (1:ℝ) else 0
  rw [one_mul,ite_eq_left hcolor]
  exact zero_lt_one
lemma typical_sample_palette {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) {y : ℂ}
    (hy : TypicalSampling c y 1) :
    ∀ᵐ t ∂angularMeasure, t ∈ paletteSet c hc y (c (y+direction t)) := by
  exact (ae_all_iff.mpr (exact_sample_palette_fixed c hc hy)).mono
    (fun t ht => ht (c (y+direction t)) rfl)
lemma ae_circle_palette_exclusion {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
    (hw : WeakColoring k c) (x : ℂ) :
    ∀ᵐ t ∂angularMeasure, ∀ᵐ v ∂angularMeasure,
      c (x+direction t+direction v) ∉ palette c hc x t := by
  have hh := Measure.ae_ae_of_ae_prod (ae_all_iff.mpr (fun i => palette_first_exclusion c hc hw x i))
  apply hh.mono
  intro t ht
  apply ht.mono
  intro v hv hmem
  apply hv (c (x+direction t+direction v)) ((mem_palette c hc x t _).mp hmem)
  simp only [angularSum,Complex.ofReal_one,one_mul]
lemma ae_circle_typicalSampling {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (x : ℂ) :
    ∀ᵐ t ∂angularMeasure, TypicalSampling c (x+direction t) 1 := by
  have htyp := Measure.ae_ae_of_ae_prod ((angularSum_quasiMeasurePreserving x (by norm_num : (1:ℝ)≠0)).ae (ae_density_actual c hc))
  apply htyp.mono
  intro t ht
  refine ⟨by norm_num,?_⟩
  simpa only [Typical,angularSum,Complex.ofReal_one,one_mul] using ht
lemma two_complement_pred {α : Type*} [Fintype α] [DecidableEq α] {S : Finset α} {i j a : α}
    (hcomp : Finset.univ\S={i,j}) (hnot : a∉S) (P : α → Prop) (hp : P a) : P i ∨ P j := by
  have ha : a∈({i,j} : Finset α) := by rw [← hcomp]; simp only [Finset.mem_sdiff,Finset.mem_univ,true_and]; exact hnot
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with h|h
  · exact Or.inl (h ▸ hp)
  · exact Or.inr (h ▸ hp)
lemma circle_complement_binary {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
    {x : ℂ} {t : Angles} {S : Finset (Fin k)} {i j : Fin k}
    (hcomp : Finset.univ\S={i,j}) (hsub : S ⊆ palette c hc x t)
    (ht : ∀ᵐ v ∂angularMeasure, c (x+direction t+direction v) ∉ palette c hc x t)
    (hy : TypicalSampling c (x+direction t) 1) : BinaryCenter c hc (x+direction t) i j := by
  apply (ht.and (typical_sample_palette c hc hy)).mono
  intro v hv
  exact two_complement_pred hcomp (fun hq => hv.1 (hsub hq))
    (fun a => v ∈ paletteSet c hc (x+direction t) a) hv.2
lemma palette_triple_null (c : ℂ → Fin 5) (hc : Measurable c) (hw : WeakColoring 5 c)
    (x : ℂ) (S : Finset (Fin 5)) (hS : S.card=3) :
    ∀ᵐ t ∂angularMeasure, ¬ S ⊆ palette c hc x t := by
  have hSc : (Finset.univ\S).card=2 := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]; simp [hS]
  obtain ⟨i,j,_,hcomp⟩ := Finset.card_eq_two.mp hSc
  filter_upwards [ae_circle_palette_exclusion c hc hw x,ae_circle_typicalSampling c hc x,
    ae_not_binary_circle c hc hw x i j] with t ht hy hn
  exact fun hsub => hn (circle_complement_binary c hc hcomp hsub ht hy)
lemma palette_cardinality (c : ℂ → Fin 5) (hc : Measurable c) (hw : WeakColoring 5 c) (x : ℂ) :
    ∀ᵐ t ∂angularMeasure, 1 ≤ (palette c hc x t).card ∧ (palette c hc x t).card ≤ 2 := by
  filter_upwards [palette_nonempty c hc x,ae_all_iff.mpr (fun S : Finset (Fin 5) =>
    ae_all_iff.mpr (fun hS : S.card=3 => palette_triple_null c hc hw x S hS))] with t ht htriple
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr ht),?_⟩
  by_contra! hcard
  obtain ⟨S,hsub,hS⟩ := Finset.exists_subset_card_eq (by omega : 3 ≤ (palette c hc x t).card)
  exact htriple S hS hsub
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
def triangleAngle : ℝ := Real.arccos (5/6)
lemma triangleAngle_cos : Real.cos triangleAngle=5/6 := by
  exact Real.cos_arccos (by norm_num) (by norm_num)
lemma triangleAngle_pos : 0<triangleAngle := Real.arccos_pos.mpr (by norm_num)
lemma triangleAngle_lt_pi : triangleAngle<Real.pi := Real.arccos_lt_pi.mpr (by norm_num)
lemma triangleAngle_ratio_irrational : Irrational (triangleAngle/Real.pi) := by
  rintro ⟨q,hq⟩
  have hh := niven (θ := triangleAngle) ⟨q,(div_eq_iff Real.pi_ne_zero).mp hq.symm⟩
    ⟨5/6,by norm_num only [Rat.cast_div,Rat.cast_ofNat]; exact triangleAngle_cos⟩
  rw [triangleAngle_cos] at hh
  norm_num at hh
lemma triangle_rotation_ergodic :
    Ergodic (fun t : Angles => ((2*triangleAngle : ℝ) : Angles)+t) angularMeasure := by
  apply ergodic_add_left_of_denseRange_zsmul _ angularMeasure
  apply AddCircle.denseRange_zsmul_coe_iff.mpr
  convert triangleAngle_ratio_irrational using 1
  field_simp
lemma equal_triangleAngle_positive {s : Angles → Bool} (hs : Measurable s)
    (hflip : ∀ᵐ t∂angularMeasure, s (t+(Real.pi/3 : ℝ))= !(s t)) :
    0<angularMeasure {t | s t=s (t+(triangleAngle : Angles))} := by
  by_contra hz
  have hz' : angularMeasure {t | s t=s (t+(triangleAngle : Angles))}=0 := le_antisymm (le_of_not_gt hz) bot_le
  have hf : ∀ᵐ t∂angularMeasure, s (t+(triangleAngle : Angles))= !(s t) := by
    filter_upwards [(measure_eq_zero_iff_ae_notMem.mp hz')] with t ht
    change ¬s t=s (t+(triangleAngle : Angles)) at ht
    cases h₁ : s t <;> cases h₂ : s (t+(triangleAngle : Angles)) <;> simp_all
  have hf₂ := (measurePreserving_add_right angularMeasure (triangleAngle : Angles)).quasiMeasurePreserving.ae hf
  have hinv : (fun t : Angles => s (((2*triangleAngle : ℝ) : Angles)+t))=ᵐ[angularMeasure] s := by
    filter_upwards [hf,hf₂] with t ht ht'
    have he : ((2*triangleAngle : ℝ) : Angles)+t=(t+(triangleAngle : Angles))+(triangleAngle : Angles) := by
      have hh : ((2*triangleAngle : ℝ) : Angles)=(triangleAngle : Angles)+(triangleAngle : Angles) := by
        calc ((2*triangleAngle : ℝ) : Angles) = ((triangleAngle+triangleAngle : ℝ) : Angles) := congrArg (fun x : ℝ => (x : Angles)) (two_mul triangleAngle)
          _ = _ := AddCircle.coe_add _ _ _
      rw [hh]
      abel
    rw [he,ht',ht,Bool.not_not]
  obtain ⟨b,hb⟩ := triangle_rotation_ergodic.ae_eq_const_of_ae_eq_comp₀ hs.nullMeasurable hinv
  have hb' := (measurePreserving_add_right angularMeasure ((Real.pi/3:ℝ) : Angles)).quasiMeasurePreserving.ae hb
  have hfalse : ∀ᵐ t∂angularMeasure, False := by
    filter_upwards [hflip,hb,hb'] with t ht ht' ht''
    change s t=b at ht'
    change s (t+((Real.pi/3:ℝ):Angles))=b at ht''
    rw [ht',ht''] at ht
    cases b <;> cases ht
  have hh : (1:ENNReal)=0 := by simpa using (ae_iff.mp hfalse)
  exact one_ne_zero hh
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma circle_exp_sub_norm_sq (a b : ℝ) :
    ‖(Circle.exp a : ℂ)-(Circle.exp b : ℂ)‖^2=2-2*Real.cos (a-b) := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply,Circle.coe_exp,Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin]
  rw [Real.cos_sub]
  nlinarith [Real.cos_sq_add_sin_sq a,Real.cos_sq_add_sin_sq b]
def sourceTriangle (x : ℂ) (t : ℝ) (j : Fin 3) : ℂ :=
  angularSum x 1 (angleChart (t+2*(j:ℝ)*(Real.pi/3),t+2*(j:ℝ)*(Real.pi/3)+Real.pi+triangleAngle))
lemma sourceTriangle_eq (x : ℂ) (t : ℝ) (j : Fin 3) :
    sourceTriangle x t j=x+(Circle.exp t : ℂ)*(Circle.exp (2*(j:ℝ)*(Real.pi/3)) : ℂ)*
      (1-(Circle.exp triangleAngle : ℂ)) := by
  simp only [sourceTriangle,angularSum,angleChart,Complex.ofReal_one,one_mul,direction_real,
    Circle.exp_add,Circle.coe_mul]
  have hpi : (Circle.exp Real.pi : ℂ)= -1 := by
    simp [Circle.coe_exp,Complex.exp_mul_I]
  rw [hpi]
  ring
lemma sourceTriangle_pair (x : ℂ) (t : ℝ) (i j : Fin 3) (hne : i≠j) :
    ‖sourceTriangle x t i-sourceTriangle x t j‖=1 := by
  have hγ : ‖(1:ℂ)-(Circle.exp triangleAngle : ℂ)‖^2=1/3 := by
    have hh := circle_exp_sub_norm_sq 0 triangleAngle
    norm_num only [Circle.exp_zero,Circle.coe_one,zero_sub,Real.cos_neg,triangleAngle_cos] at hh ⊢
    exact hh
  have hc₂ : Real.cos (2*(Real.pi/3))= -1/2 := by
    rw [Real.cos_two_mul,Real.cos_pi_div_three]; norm_num
  have hc₄ : Real.cos (4*(Real.pi/3))= -1/2 := by
    rw [show 4*(Real.pi/3)=2*(2*(Real.pi/3)) by ring,Real.cos_two_mul,hc₂]; norm_num
  have hd : ‖(Circle.exp (2*(i:ℝ)*(Real.pi/3)) : ℂ)-(Circle.exp (2*(j:ℝ)*(Real.pi/3)) : ℂ)‖^2=3 := by
    rw [circle_exp_sub_norm_sq]
    fin_cases i <;> fin_cases j <;> try contradiction
    all_goals norm_num only [Fin.val_zero,Fin.val_one,Fin.val_two,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,mul_zero,mul_one,zero_mul,sub_zero,zero_sub]
    all_goals
      simp only [show 2*(Real.pi/3)-4*(Real.pi/3)= -(2*(Real.pi/3)) by ring,
        show 4*(Real.pi/3)-2*(Real.pi/3)=2*(Real.pi/3) by ring,Real.cos_neg,hc₂,hc₄]
      norm_num
  have he : sourceTriangle x t i-sourceTriangle x t j=
      (Circle.exp t : ℂ)*((Circle.exp (2*(i:ℝ)*(Real.pi/3)) : ℂ)-
        (Circle.exp (2*(j:ℝ)*(Real.pi/3)) : ℂ))*(1-(Circle.exp triangleAngle : ℂ)) := by
    rw [sourceTriangle_eq,sourceTriangle_eq]; ring
  rw [he,norm_mul,norm_mul,Circle.norm_coe,one_mul]
  have hn := norm_nonneg ((Circle.exp (2*(i:ℝ)*(Real.pi/3)) : ℂ)-(Circle.exp (2*(j:ℝ)*(Real.pi/3)) : ℂ))
  have hm := norm_nonneg ((1:ℂ)-(Circle.exp triangleAngle : ℂ))
  have heq : (‖(Circle.exp (2*(i:ℝ)*(Real.pi/3)) : ℂ)-(Circle.exp (2*(j:ℝ)*(Real.pi/3)) : ℂ)‖ *
      ‖(1:ℂ)-(Circle.exp triangleAngle : ℂ)‖)^2=1 := by
    rw [mul_pow,hd,hγ]; norm_num
  nlinarith [mul_nonneg hn hm]
end EuclideanFiveColor
end

end OAI
