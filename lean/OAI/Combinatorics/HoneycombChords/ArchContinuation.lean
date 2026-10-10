import OAI.Combinatorics.HoneycombChords.BoundarySystems

namespace OAI

/-! Arch continuation for critical honeycomb strips.

The formulas follow the finite strip transfer calculation in the companion paper
on uniform marked polygon estimates. -/

section

namespace CriticalHoneycomb.FiniteContinuation

def halfRect (W : ℕ) : Set Center := {v | 0≤v.1 ∧ v.1<(W:ℤ) ∧ 0≤v.2.1}
def BottomArch (W : ℕ) (i j : Fin (W+1)) :=
  {p : List Center // IsTrace (halfRect (W+1)) p ∧
    p.head?=some (up i.val 0) ∧ p.getLast?=some (up j.val 0)}

def archRun (j : ℕ) : List Center := (row 0 0 (j+1)).reverse
lemma archRun_head (j : ℕ) : (archRun j).head?=some (down j 0) := by
  simp [archRun,row_last]
lemma archRun_last (j : ℕ) : (archRun j).getLast?=some (up 0 0) := by
  simp [archRun,row_head]
lemma archRun_mem (j : ℕ) (v : Center) (hv : v∈archRun j) :
    0≤v.1 ∧ v.1≤j ∧ v.2.1=0 := by
  rw [archRun,List.mem_reverse] at hv
  have hh := (mem_row 0 0 (j+1) v).mp hv
  simp only [Nat.cast_add,Nat.cast_one,zero_add] at hh
  omega

lemma eastRun_min (W : ℕ) (i : Fin W) (j : ℤ) {v : Center}
    (hv : v∈eastRun W i j) : (i.val : ℤ)≤v.1 := by
  simp only [eastRun,List.mem_reverse,List.mem_cons] at hv
  rcases hv with rfl|hv
  · simp [down]
  · have hh := (mem_row _ _ _ _).mp hv
    omega

noncomputable def archExtend {W : ℕ} {i j : Fin (W+1)} (γ : BottomArch W i j) : List Center :=
  eastRun (W+1) i 0++γ.val.map (shift 1)++archRun j.val
lemma archExtend_head {W : ℕ} {i j : Fin (W+1)} (γ : BottomArch W i j) :
    (archExtend γ).head?=some (down W 0) := by
  simp [archExtend,List.head?_append,eastRun_head]
lemma archExtend_last {W : ℕ} {i j : Fin (W+1)} (γ : BottomArch W i j) :
    (archExtend γ).getLast?=some (up 0 0) := by
  simp [archExtend,List.getLast?_append,archRun_last]
lemma archExtend_length {W : ℕ} {i j : Fin (W+1)} (γ : BottomArch W i j) :
    (archExtend γ).length≤γ.val.length+4*(W+1) := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [archExtend,archRun,List.length_append,List.length_map,List.length_reverse,
    row_length,eastRun_length]
  omega
lemma archExtend_chain {W : ℕ} {i j : Fin (W+1)} (γ : BottomArch W i j) :
    (archExtend γ).IsChain Adj := by
  have hm : (γ.val.map (shift 1)).IsChain Adj :=
    List.isChain_map_of_isChain _ (fun _ _ hh=>(shift_adj 1 _ _).mpr hh) γ.property.1.2.1
  have hw : (archRun j.val).IsChain Adj := reverse_chain (row_chain 0 0 (j.val+1))
  unfold archExtend
  apply ((eastRun_chain _ _ _).append hm ?_).append hw
  · simp only [List.getLast?_append,List.getLast?_map,γ.property.2.2,Option.map_some,
      Option.some_or,archRun_head,Option.mem_def,Option.some.injEq]
    intro u hu v hv
    subst u;subst v
    simp [shift,Adj,up,down]
  · simp only [eastRun_last,List.head?_map,γ.property.2.1,Option.map_some,Option.mem_def,
      Option.some.injEq]
    intro u hu v hv
    subst u;subst v
    simp [shift,Adj,up,down]
lemma archExtend_nodup {W : ℕ} {i j : Fin (W+1)} (hji : j < i) (γ : BottomArch W i j) :
    (archExtend γ).Nodup := by
  have hn := γ.property.1.1
  have hp := γ.property.1.2.2
  have hm := hn.map (shift_injective 1)
  have hd₁ : List.Disjoint (eastRun (W+1) i 0) (γ.val.map (shift 1)) := by
    intro v hv hv'
    have hr := eastRun_mem (W+1) i 0 hv
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv'
    have hh := hp u hu
    simp only [halfRect,Set.mem_ofPred_eq,shift] at hh hr
    omega
  have hd₂ : List.Disjoint (eastRun (W+1) i 0) (archRun j.val) := by
    intro v hv hv'
    have h₁ := eastRun_min (W+1) i 0 hv
    have h₂ := archRun_mem j.val v hv'
    have hji : j.val < i.val := hji
    omega
  have hd₃ : List.Disjoint (γ.val.map (shift 1)) (archRun j.val) := by
    intro v hv hv'
    have hr := archRun_mem j.val v hv'
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
    have hh := hp u hu
    simp only [halfRect,Set.mem_ofPred_eq,shift] at hh hr
    omega
  simp only [archExtend,List.nodup_append]
  refine ⟨⟨eastRun_nodup _ _ _,hm,?_⟩,?_,?_⟩
  · intro a ha b hb hab;subst b;exact hd₁ ha hb
  · simpa [archRun] using row_nodup 0 0 (j.val+1)
  · intro a ha b hb hab;subst b
    rcases List.mem_append.mp ha with ha|ha
    · exact hd₂ ha hb
    · exact hd₃ ha hb

def aboveZero (v : Center) : Bool := decide (0<v.2.1)
lemma archExtend_filter {W : ℕ} {i j : Fin (W+1)} (γ : BottomArch W i j) :
    (archExtend γ).filter aboveZero=γ.val.map (shift 1) := by
  have he : (eastRun (W+1) i 0).filter aboveZero=[] := by
    rw [List.filter_eq_nil_iff]
    intro v hv
    have hh:=eastRun_mem (W+1) i 0 hv
    simp [aboveZero,hh.2.2]
  have hw : (archRun j.val).filter aboveZero=[] := by
    rw [List.filter_eq_nil_iff]
    intro v hv
    have hh:=archRun_mem j.val v hv
    simp [aboveZero,hh.2.2]
  have hm : (γ.val.map (shift 1)).filter aboveZero=γ.val.map (shift 1) := by
    rw [List.filter_eq_self]
    intro v hv
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
    have hh:=γ.property.1.2.2 u hu
    simp only [halfRect,Set.mem_ofPred_eq] at hh
    simp [aboveZero,shift]
    omega
  simp [archExtend,List.filter_append,he,hw,hm]
lemma archExtend_injective {W : ℕ} {i j : Fin (W+1)} :
    Function.Injective (archExtend (W:=W) (i:=i) (j:=j)) := by
  intro γ δ he
  apply Subtype.ext
  have hh:=congrArg (List.filter aboveZero) he
  rw [archExtend_filter,archExtend_filter] at hh
  exact List.map_injective_iff.mpr (shift_injective 1) hh

lemma finite_arch_bound {W : ℕ} {i j : Fin (W+1)} (s : Finset (BottomArch W i j)) :
    ∃ N : ℕ,∀ γ∈s,∀ v∈γ.val,v.2.1≤N := by
  classical
  let t : Finset ℕ := s.biUnion (fun γ=>γ.val.toFinset.image (fun v=>v.2.1.natAbs))
  refine ⟨t.sup id,?_⟩
  intro γ hγ v hv
  have ht : v.2.1.natAbs∈t := by
    apply Finset.mem_biUnion.mpr
    exact ⟨γ,hγ,Finset.mem_image.mpr ⟨v,List.mem_toFinset.mpr hv,rfl⟩⟩
  have hh : v.2.1.natAbs≤t.sup id := Finset.le_sup (f:=id) ht
  have ha : v.2.1≤(v.2.1.natAbs:ℤ) := Int.le_natAbs
  omega

lemma archExtend_mem {W N : ℕ} {i j : Fin (W+1)} (γ : BottomArch W i j)
    (hb : ∀ v∈γ.val,v.2.1≤N) :
    ∀ v∈archExtend γ,v∈rect (W+1) (N+2) := by
  intro v hv
  simp only [archExtend,List.mem_append] at hv
  rcases hv with (hv|hv)|hv
  · have hh:=eastRun_mem (W+1) i 0 hv
    have hi:=i.isLt
    simp only [rect,Set.mem_ofPred_eq]
    omega
  · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
    have hh:=γ.property.1.2.2 u hu
    have hu:=hb u hu
    simp only [halfRect,Set.mem_ofPred_eq] at hh
    simp only [rect,Set.mem_ofPred_eq,shift]
    omega
  · have hh:=archRun_mem j.val v hv
    have hj:=j.isLt
    simp only [rect,Set.mem_ofPred_eq]
    omega
end CriticalHoneycomb.FiniteContinuation

namespace CriticalHoneycomb.FiniteContinuation
open CriticalHoneycomb.Transfer
noncomputable def archChord {W N : ℕ} {i j : Fin (W+1)} (hji : j < i)
    (γ : BottomArch W i j) (hb : ∀ v∈γ.val,v.2.1≤N) :
    RasterGrid.RectChord W (N+1) 0 0 := by
  refine ⟨(archExtend γ).reverse,⟨by simpa using archExtend_nodup hji γ,
    reverse_chain (archExtend_chain γ),?_⟩,?_,?_⟩
  · intro v hv
    have hh := archExtend_mem γ hb v (List.mem_reverse.mp hv)
    apply (RasterGrid.mem_domain_iff v).mpr
    simp only [rect,Set.mem_ofPred_eq] at hh
    simp only [Nat.cast_add,Nat.cast_one]
    omega
  · simp [List.head?_reverse,archExtend_last,RasterGrid.westPort,RasterGrid.cellCenter,up]
  · simp [List.getLast?_reverse,archExtend_head,RasterGrid.eastPort,RasterGrid.cellCenter,down]

lemma archChord_injective {W N : ℕ} {i j : Fin (W+1)} (hji : j < i)
    (s : Finset (BottomArch W i j)) (hb : ∀ γ∈s,∀ v∈γ.val,v.2.1≤N) :
    Function.Injective (fun γ : {γ // γ∈s}=>archChord hji γ.val (hb γ.val γ.property)) := by
  intro γ δ he
  have hh := congrArg (fun p : RasterGrid.RectChord W (N+1) 0 0=>p.val.reverse) he
  simp only [archChord,List.reverse_reverse] at hh
  exact Subtype.ext (archExtend_injective hh)

lemma arch_extended_weight {W : ℕ} {i j : Fin (W+1)} (γ : BottomArch W i j) :
    kappa^(4*(W+1))*kappa^γ.val.length≤kappa^(archExtend γ).length := by
  rw [←pow_add]
  apply pow_le_pow_of_le_one kappa_positive.le kappa_at_most_one
  have hh:=archExtend_length γ
  omega

theorem arch_partial_sum_le {W : ℕ} {i j : Fin (W+1)} (hji : j < i)
    (s : Finset (BottomArch W i j)) :
    kappa^(4*(W+1))*(∑ γ∈s,kappa^γ.val.length)≤1 := by
  classical
  obtain ⟨N,hN⟩ := finite_arch_bound s
  let B := Σ k : Fin (N+2),RasterGrid.RectChord W (N+1) k 0
  let f : {γ // γ∈s} → B := fun γ=>⟨0,archChord hji γ.val (hN γ.val γ.property)⟩
  have hi : Function.Injective f := by
    intro γ δ he
    have hh : (archExtend γ.val).reverse=(archExtend δ.val).reverse :=
      congrArg (fun p : B=>p.2.val) he
    apply Subtype.ext
    apply archExtend_injective
    exact List.reverse_injective hh
  have hb : (∑ p : B,kappa^p.2.val.length)≤1 := by
    rw [Fintype.sum_sigma]
    exact FluxWard.rectangle_actual_sum_bound W (N+1) 0
  calc
    kappa^(4*(W+1))*(∑ γ∈s,kappa^γ.val.length) =
      ∑ γ : {γ // γ∈s},kappa^(4*(W+1))*kappa^γ.val.val.length := by
        rw [Finset.mul_sum]
        exact Finset.sum_subtype s (fun _=>Iff.rfl) _
    _ ≤ ∑ γ : {γ // γ∈s},kappa^(f γ).2.val.length := by
      apply Finset.sum_le_sum
      intro γ hγ
      simpa only [f,archChord,List.length_reverse] using arch_extended_weight γ.val
    _ = ∑ p∈Finset.univ.image f,kappa^p.2.val.length :=
      (Finset.sum_image (f:=fun p : B=>kappa^p.2.val.length) (s:=Finset.univ) hi.injOn).symm
    _ ≤ ∑ p : B,kappa^p.2.val.length := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro p hp hn
      exact (pow_pos kappa_positive _).le
    _ ≤ 1 := hb

theorem bottom_arch_summable_of_lt {W : ℕ} {i j : Fin (W+1)} (hji : j < i) :
    Summable (fun γ : BottomArch W i j=>kappa^γ.val.length) := by
  apply summable_of_sum_le (c:=1/kappa^(4*(W+1)))
  · intro γ
    exact (pow_pos kappa_positive _).le
  · intro s
    apply (le_div_iff₀ (pow_pos kappa_positive _)).mpr
    simpa only [mul_comm] using arch_partial_sum_le hji s

def reverseArch {W : ℕ} {i j : Fin (W+1)} (γ : BottomArch W i j) : BottomArch W j i :=
  ⟨γ.val.reverse,⟨List.nodup_reverse.mpr γ.property.1.1,
    reverse_chain γ.property.1.2.1,fun v hv=>γ.property.1.2.2 v (List.mem_reverse.mp hv)⟩,
    by simpa only [List.head?_reverse] using γ.property.2.2,
    by simpa only [List.getLast?_reverse] using γ.property.2.1⟩

def reverseArchEquiv {W : ℕ} (i j : Fin (W+1)) : BottomArch W i j ≃ BottomArch W j i where
  toFun := reverseArch
  invFun := reverseArch
  left_inv γ := by apply Subtype.ext; exact List.reverse_reverse _
  right_inv γ := by apply Subtype.ext; exact List.reverse_reverse _

theorem bottom_arch_summable {W : ℕ} {i j : Fin (W+1)} (hne : i≠j) :
    Summable (fun γ : BottomArch W i j=>kappa^γ.val.length) := by
  rcases lt_or_gt_of_ne hne with hij|hji
  · have hh := bottom_arch_summable_of_lt hij
    have he := (reverseArchEquiv i j).summable_iff.mpr hh
    change Summable (fun γ : BottomArch W i j=>kappa^γ.val.reverse.length) at he
    simpa only [List.length_reverse] using he
  · exact bottom_arch_summable_of_lt hji
end CriticalHoneycomb.FiniteContinuation

namespace CriticalHoneycomb.FiniteContinuation
open Filter Topology

structure ArchEnds (W : ℕ) where
  first : Fin (W+1)
  last : Fin (W+1)
  distinct : first≠last

def ArchFamily {W : ℕ} : List (ArchEnds W) → Type
  | [] => PUnit
  | a::as => BottomArch W a.first a.last × ArchFamily as

def archNodes {W : ℕ} : {as : List (ArchEnds W)} → ArchFamily as → List Center
  | [],_ => []
  | _::_,γ => γ.1.val++archNodes γ.2

noncomputable def archFamilyWeight {W : ℕ} {as : List (ArchEnds W)}
    (γ : ArchFamily as) : ℝ := kappa^(archNodes γ).length

lemma archFamilyWeight_nonnegative {W : ℕ} {as : List (ArchEnds W)} (γ : ArchFamily as) :
    0≤archFamilyWeight γ := (pow_pos kappa_positive _).le

lemma arch_family_summable {W : ℕ} (as : List (ArchEnds W)) :
    Summable (archFamilyWeight (as:=as)) := by
  induction as with
  | nil =>
    change Summable (fun _ : PUnit=>kappa^([] : List Center).length)
    exact (hasSum_fintype _).summable
  | cons a as ih =>
    change Summable (fun γ : BottomArch W a.first a.last × ArchFamily as =>
      kappa^(γ.1.val++archNodes γ.2).length)
    simp only [List.length_append,pow_add]
    apply (summable_prod_of_nonneg (fun γ=>mul_nonneg
      (pow_pos kappa_positive _).le (pow_pos kappa_positive _).le)).mpr
    refine ⟨fun γ=>ih.mul_left (kappa^γ.val.length),?_⟩
    simpa only [tsum_mul_left,archFamilyWeight] using
      (bottom_arch_summable a.distinct).mul_right (∑' δ : ArchFamily as,archFamilyWeight δ)

def ArchSystem {W : ℕ} (as : List (ArchEnds W)) :=
  {γ : ArchFamily as // (archNodes γ).Nodup}

noncomputable def archSystemWeight {W : ℕ} {as : List (ArchEnds W)} (γ : ArchSystem as) : ℝ :=
  archFamilyWeight γ.val

lemma arch_system_summable {W : ℕ} (as : List (ArchEnds W)) :
    Summable (archSystemWeight (as:=as)) := (arch_family_summable as).subtype _

lemma archNodes_mem {W : ℕ} {as : List (ArchEnds W)} (γ : ArchFamily as) :
    ∀ v∈archNodes γ,0≤v.1 ∧ v.1<(W+1:ℕ) ∧ 0≤v.2.1 := by
  induction as with
  | nil => simp [archNodes]
  | cons a as ih =>
    intro v hv
    rcases List.mem_append.mp hv with hv|hv
    · exact γ.1.property.1.2.2 v hv
    · exact ih γ.2 v hv

noncomputable def archHeight {W : ℕ} {as : List (ArchEnds W)} (γ : ArchFamily as) : ℕ :=
  (archNodes γ).toFinset.sup (fun v=>v.2.1.natAbs)

lemma archNodes_height {W : ℕ} {as : List (ArchEnds W)} (γ : ArchFamily as)
    {v : Center} (hv : v∈archNodes γ) : v.2.1≤(archHeight γ:ℤ) := by
  have hh : v.2.1.natAbs≤archHeight γ := Finset.le_sup (f:=fun v : Center=>v.2.1.natAbs) (List.mem_toFinset.mpr hv)
  have ha : v.2.1≤(v.2.1.natAbs:ℤ) := Int.le_natAbs
  omega

def topTurn (W h : ℕ) (v : Center) : Center := ((W:ℤ)-v.1,(h:ℤ)-v.2.1,!v.2.2)
lemma topTurn_injective (W h : ℕ) : Function.Injective (topTurn W h) := by
  rintro ⟨x,y,b⟩ ⟨x',y',b'⟩ he
  simp only [topTurn,Prod.mk.injEq] at he
  rcases he with ⟨hx,hy,hb⟩
  have hxx : x=x' := by omega
  have hyy : y=y' := by omega
  have hb' : b=b' := by simpa using congrArg Bool.not hb
  subst x';subst y';subst b'
  rfl
lemma topTurn_adj (W h : ℕ) (v w : Center) :
    Adj (topTurn W h v) (topTurn W h w) ↔ Adj v w := by
  rcases v with ⟨x,y,b⟩;rcases w with ⟨x',y',b'⟩
  cases b <;> cases b' <;> simp [topTurn,Adj] <;> omega

noncomputable def archSystemNodes {W : ℕ} {as bs : List (ArchEnds W)}
    (h : ℕ) (γ : ArchSystem as) (δ : ArchSystem bs) : List Center :=
  archNodes γ.val++(archNodes δ.val).map (topTurn W h)

def ArchSystemsFit {W : ℕ} {as bs : List (ArchEnds W)}
    (h : ℕ) (γ : ArchSystem as) (δ : ArchSystem bs) : Prop :=
  (archSystemNodes h γ δ).Nodup ∧
    ∀ v∈archSystemNodes h γ δ,v∈rect (W+1) (h+1)

lemma archSystemsFit_of_height {W h : ℕ} {as bs : List (ArchEnds W)}
    (γ : ArchSystem as) (δ : ArchSystem bs)
    (hh : archHeight γ.val+archHeight δ.val<h) : ArchSystemsFit h γ δ := by
  constructor
  · apply List.Nodup.append γ.property (δ.property.map (topTurn_injective W h))
    intro v hv hv'
    obtain ⟨u,hu,hvu⟩ := List.mem_map.mp hv'
    have hγ:=archNodes_height γ.val hv
    have hδ:=archNodes_height δ.val hu
    have he:=congrArg (fun v : Center=>v.2.1) hvu
    simp only [topTurn] at he
    omega
  · intro v hv
    rcases List.mem_append.mp hv with hv|hv
    · have hm:=archNodes_mem γ.val v hv
      have hγ:=archNodes_height γ.val hv
      simp only [rect,Set.mem_ofPred_eq]
      omega
    · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
      have hm:=archNodes_mem δ.val u hu
      have hδ:=archNodes_height δ.val hu
      simp only [rect,Set.mem_ofPred_eq,topTurn]
      omega

lemma eventually_archSystemsFit {W : ℕ} {as bs : List (ArchEnds W)}
    (γ : ArchSystem as) (δ : ArchSystem bs) :
    ∀ᶠ h : ℕ in atTop,ArchSystemsFit h γ δ := by
  filter_upwards [eventually_gt_atTop (archHeight γ.val+archHeight δ.val)] with h hh
  exact archSystemsFit_of_height γ δ hh

noncomputable def halfStripSystemMass {W : ℕ} (as : List (ArchEnds W)) : ℝ :=
  ∑' γ : ArchSystem as,archSystemWeight γ

noncomputable def finitePureArchMass {W : ℕ} (as bs : List (ArchEnds W)) (h : ℕ) : ℝ := by
  classical
  exact ∑' p : ArchSystem as × ArchSystem bs,
    if ArchSystemsFit h p.1 p.2 then archSystemWeight p.1*archSystemWeight p.2 else 0

theorem pure_arch_limit {W : ℕ} (as bs : List (ArchEnds W)) :
    Tendsto (finitePureArchMass as bs) atTop
      (𝓝 (halfStripSystemMass as*halfStripSystemMass bs)) := by
  classical
  have hn : ∀ p : ArchSystem as × ArchSystem bs,
      0≤archSystemWeight p.1*archSystemWeight p.2 := fun p=>
    mul_nonneg (archFamilyWeight_nonnegative p.1.val) (archFamilyWeight_nonnegative p.2.val)
  have hs : Summable (fun p : ArchSystem as × ArchSystem bs=>
      archSystemWeight p.1*archSystemWeight p.2) := by
    apply (summable_prod_of_nonneg hn).mpr
    refine ⟨fun γ=>(arch_system_summable bs).mul_left (archSystemWeight γ),?_⟩
    simpa only [tsum_mul_left,halfStripSystemMass] using
      (arch_system_summable as).mul_right (halfStripSystemMass bs)
  have he : (∑' p : ArchSystem as × ArchSystem bs,archSystemWeight p.1*archSystemWeight p.2) =
      halfStripSystemMass as*halfStripSystemMass bs := by
    exact ((arch_system_summable as).hasSum.mul (arch_system_summable bs).hasSum hs).tsum_eq
  rw [←he]
  apply tendsto_tsum_of_dominated_convergence hs
  · intro p
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_archSystemsFit p.1 p.2] with h hh
    simp only [hh,ite_eq_left]
  · apply Eventually.of_forall
    intro h p
    split_ifs
    · rw [Real.norm_eq_abs,abs_of_nonneg (hn p)]
    · simp only [norm_zero]
      exact hn p
end CriticalHoneycomb.FiniteContinuation

end

end OAI
