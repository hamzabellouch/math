import Mathlib
import OAI.Geometry.BallPacking.Hamiltonian.ScaledPlanarMotion

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology BigOperators
open Set Function

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem scaled_disk_slice_iff (Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1))
    {a χ : P → ℝ} (y : P) (ha : a y ≠ 0) (t : ℝ) (x : Plane) {L : ℝ}
    (hfit : χ y ≠ 0 → (a y)^2 ≤ L) :
    radialArea (scaledPlanarTrace Ψ.motion a χ y t x) ≤ L ↔ radialArea x ≤ L := by
  refine ⟨?_,fun hx => scaled_disk_preserves_slice Ψ y ha t x hx hfit⟩
  intro hx
  by_contra hn
  by_cases hc : χ y = 0
  · rw [scaledPlanarTrace_cutoff_zero Ψ.motion y ha hc] at hx
    exact hn hx
  · have hh : (a y)^2 ≤ radialArea x := (hfit hc).trans (le_of_not_ge hn)
    rw [scaled_disk_fixed Ψ y ha t x hh] at hx
    exact hn hx

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Topology BigOperators
open Set Function
open Hamiltonian Comparison

variable {m N : ℕ}

def planeRegion (b : Fin N → Moments m) (c : Fin N → ℝ) : Set (PlanePhase (Fin m)) :=
  planeMoments ⁻¹' region b c

@[simp] theorem assemble_outerMoments (j : Fin m) (z : PlanePhase (Fin m)) :
    assemble j (baseProjection j (outerMoments j z)) (radialArea (z j)) = planeMoments z := by
  funext i
  by_cases hi : i=j
  · subst i; simp [planeMoments]
  · simp [assemble,hi,baseProjection,planeMoments]

@[simp] theorem baseProjection_outerMoments (j : Fin m) (z : PlanePhase (Fin m)) :
    baseProjection j (outerMoments j z) = baseProjection j (planeMoments z) := by
  funext i
  simp [baseProjection,planeMoments,i.property]

theorem planeRegion_mem_iff (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m)
    [Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i) (z : PlanePhase (Fin m)) :
    z ∈ planeRegion b c ↔ outerMoments j z ∈ fullBase b c j ∧
      radialArea (z j) ≤ fullLength b c j (outerMoments j z) := by
  have hh := assemble_mem_iff b c j hb
    (baseProjection j (outerMoments j z)) (radialArea (z j))
  rw [assemble_outerMoments] at hh
  change planeMoments z ∈ region b c ↔ _
  simpa only [fullBase,mem_ofPred_eq,outerMoments_self,and_true,true_and,
    radialArea_nonneg,fullLength] using hh

def globalSliceFamily (F : C(Moments m,ℝ)) (j : Fin m) : C(Moments m × ℝ,ℝ) where
  toFun p := F (assemble j (baseProjection j p.1) p.2)
  continuous_toFun := F.continuous.comp (by
    apply continuous_pi
    intro i
    by_cases hi : i=j
    · simp only [assemble,hi,dite_eq_left]; exact continuous_snd
    · simp only [assemble,dite_eq_right hi,baseProjection]
      exact (continuous_apply i).comp continuous_fst)

theorem globalSliceFamily_convex (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m)
    [Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i)
    (F : C(Moments m,ℝ)) (hF : ConvexOn ℝ (region b c) F)
    (y : Moments m) (hy : y ∈ fullBase b c j) :
    ConvexOn ℝ (Icc 0 (fullLength b c j y)) (fun h => globalSliceFamily F j (y,h)) := by
  refine ⟨convex_Icc _ _,?_⟩
  intro u hu v hv a d ha hd had
  have hu' := (assemble_mem_iff b c j hb _ u).mpr ⟨hy.2,hu⟩
  have hv' := (assemble_mem_iff b c j hb _ v).mpr ⟨hy.2,hv⟩
  have hh := hF.2 hu' hv' ha hd had
  change F (assemble j (baseProjection j y) (a*u+d*v)) ≤
    a*F (assemble j (baseProjection j y) u)+d*F (assemble j (baseProjection j y) v)
  have hey : a • baseProjection j y+d • baseProjection j y = baseProjection j y := by
    rw [←add_smul,had,one_smul]
  rw [←assemble_affine,hey] at hh
  exact hh

theorem globalSliceFamily_at_moments (F : C(Moments m,ℝ)) (j : Fin m)
    (z : PlanePhase (Fin m)) :
    globalSliceFamily F j (outerMoments j z,radialArea (z j)) = F (planeMoments z) := by
  change F (assemble j _ _) = _
  rw [assemble_outerMoments]

theorem coordRearrange_eq_intervalMinimum (b : Fin N → Moments m) (c : Fin N → ℝ)
    (j : Fin m) [Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i)
    (F : C(Moments m,ℝ)) (p : region b c) :
    coordRearrange b c j hb (F.restrict (region b c)) p =
      intervalMinimum (fiberFunction (globalSliceFamily F j) p.val)
        (fullLength b c j p.val) (p.val j) := by
  unfold coordRearrange rearrange intervalMinimum
  apply congrArg minimum
  apply ContinuousMap.ext
  intro t
  simp only [ContinuousMap.comp_apply,ContinuousMap.coe_mk,ContinuousMap.curry_apply,
    intervalValue,ContinuousMap.sup_apply,ContinuousMap.comp_apply,
    ContinuousMap.coe_mk,intervalEndpoint,onSlice,ContinuousMap.restrict_apply,
    fixedIntervalValue,fiberFunction,globalSliceFamily,zero_mul,one_mul,add_zero]
  rfl

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function MeasureTheory
open Comparison
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_hamiltonian_rounded_intervals {m : ℕ} {Y : Set P}
    (hY : IsCompact Y) (hcY : Convex ℝ Y) (y₀ : P) (hy₀ : y₀ ∈ Y)
    (h L w : Fin m → ℝ) (hh : ∀ i, 0 < h i) (hh1 : ∀ i, h i < 1)
    (hhmono : StrictMono h) (hw : ∀ i, 0 < w i) (hw1 : ∀ i, w i < 1)
    (hwmono : StrictMono w) (hL : ∀ i, L i*w i = h i)
    (c : P → Fin m → ℝ) (hc : ContDiff ℝ ∞ c)
    (V : P → Fin m → Set ℝ)
    (hV : ∀ i, IsOpen {p : P × ℝ | p.2 ∈ V p.1 i})
    (hVconv : ∀ y ∈ Y, ∀ i, Convex ℝ (V y i))
    (hVsub : ∀ y i, V y i ⊆ Ioo 0 1)
    (hplace : ∀ y ∈ Y, (∀ i, c y i ∈ V y i ∧ c y i+L i ∈ V y i) ∧
      StrictNestedStarts L (c y)) :
    ∃ Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1),
      ∀ i y, y ∈ Y → ∀ x ∈ closedRoundDisk (areaRadius (h i)),
        radialArea (Ψ.isotopy.map y 1 x) ∈ V y i := by
  have hLpos (i : Fin m) : 0 < L i := (mul_pos_iff_of_pos_right (hw i)).mp (hL i ▸ hh i)
  obtain ⟨q,k,hq,hq1,hk,hsquare,harea,hmargin⟩ :=
    exists_exact_area_rounded_margins hY c hc.continuous L w hwmono V hV hplace
  let s : ℝ := 4/squeezedArea k
  have hs : 0 < s := div_pos (by norm_num) harea
  let C (i : Fin m) (y : P) : Plane := (c y i+L i/2,1/2)
  let a (i : Fin m) := s*L i/2
  let b (i : Fin m) := w i/2
  have ha (i : Fin m) : 0 < a i := div_pos (mul_pos hs (hLpos i)) (by norm_num)
  have hb (i : Fin m) : 0 < b i := div_pos (hw i) (by norm_num)
  have hC (i : Fin m) : ContDiff ℝ ∞ (C i) :=
    ((contDiff_apply ℝ ℝ i).comp hc |>.add contDiff_const).prodMk contDiff_const
  let A : Set P := {y | RoundedMargins (fun y i => c y i+L i/2) L w V q s y}
  have hA : IsOpen A := (roundedMargins_open (fun y i => c y i+L i/2)
    (by apply continuous_pi; intro i; exact ((continuous_apply i).comp hc.continuous).add continuous_const)
    L w V hV).preimage
      (show Continuous (fun y : P => ((q,s),y)) from continuous_const.prodMk continuous_id)
  have hYA : Y ⊆ A := hmargin
  have hfit (i : Fin m) (y : P) (hy : y ∈ A) : FitsPolar (C i y) (a i) (b i) := by
    have hlo := (hVsub y i (hy.2.1 i).1).1
    have hhi := (hVsub y i (hy.2.1 i).2).2
    change 0 < c y i+L i/2-s*L i/2 ∧ c y i+L i/2+s*L i/2 < 1 ∧
      0 < 1/2-w i/2 ∧ 1/2+w i/2 < 1
    exact ⟨hlo,hhi,by linarith [hw1 i],by linarith [hw1 i]⟩
  let r i := areaRadius (h i)
  have hr i : 0 < r i := areaRadius_pos (hh i)
  have hrmono : StrictMono r := fun i j hij =>
    areaRadius_strictMono (hh i).le (hh j).le (hhmono hij)
  let f (i : Fin m) (p : P × Plane) := normalizedPolarMap k (C i p.1) (a i) (b i) (r i) p.2
  have hf (i : Fin m) : ContDiffOn ℝ ∞ (f i) (A ×ˢ univ) :=
    normalizedPolarFamily_smoothOn hA (C i) (hC i) (ha i) (hb i) k (r i) (hfit i)
  have hi (i : Fin m) (y : P) (hy : y ∈ A) : Injective (fun x => f i (y,x)) :=
    normalizedPolarMap_injective hk (ha i) (hb i) (hr i) (C i y) (hfit i y hy)
  have hd (i : Fin m) (y : P) (hy : y ∈ A) (x : Plane) :
      0 < (fderiv ℝ (fun x => f i (y,x)) x).det :=
    normalizedPolarMap_det_pos hk (ha i) (hb i) (hr i) (C i y) (hfit i y hy) x
  have himage (i : Fin m) (y : P) :
      (fun x => f i (y,x)) '' closedRoundDisk (r i) = polarRoundedDisk k (C i y) (a i) (b i) :=
    normalizedPolarMap_image (hr i) k (C i y) (a i) (b i)
  have hnest ⦃i j : Fin m⦄ (hij : i < j) (y : P) (hy : y ∈ Y) :
      (fun x => f i (y,x)) '' closedRoundDisk (r i) ⊆
        interior ((fun x => f j (y,x)) '' closedRoundDisk (r j)) := by
    rw [himage,himage]
    apply polarRoundedDisk_nested (ha j) (hb j) (hfit j y (hYA hy))
    apply roundedBox_nested_of_margins (ha i) (hb i) (ha j) (hb j) hsquare
    all_goals
      have hn := (hmargin y hy).2.2 hij
      dsimp only [C,a,b] at *
      nlinarith only [hn.1,hn.2.1,hn.2.2]
  have hrR (i : Fin m) : r i < areaRadius 1 :=
    areaRadius_strictMono (hh i).le (by norm_num) (hh1 i)
  have htarget (i : Fin m) (y : P) (hy : y ∈ Y) :
      (fun x => f i (y,x)) '' closedRoundDisk (r i) ⊆ roundDisk (areaRadius 1) := by
    intro z hz
    rw [himage] at hz
    obtain ⟨x,_,rfl⟩ := hz
    rw [mem_roundDisk_areaRadius (by norm_num)]
    change Real.pi * radiusSq _ < 1
    rw [polarRoundedMap_capacity (ha i) (hb i) k (C i y) (hfit i y (hYA hy))]
    exact (roundedMap_mem_openBox (ha i) (hb i) k (C i y) x).1.2.trans (hfit i y (hYA hy)).2.1
  have hva (i : Fin m) (y : P) (hy : y ∈ Y) :
      volume ((fun x => f i (y,x)) '' closedRoundDisk (r i)) = volume (closedRoundDisk (r i)) := by
    rw [himage,volume_closedRoundDisk_areaRadius (hh i).le]
    rw [polarRoundedDisk_volume_eq (ha i) (hb i) k (C i y) (hfit i y (hYA hy))]
    congr 1
    dsimp only [a,b,s]
    rw [←hL i]
    field_simp [harea.ne']
    ring
  obtain ⟨Ψ,hΨ⟩ := exists_hamiltonian_plane_disk_germs hY hcY hA hYA y₀ hy₀ r hr hrmono f hf hi hd hnest
    (areaRadius 1) (areaRadius_pos (by norm_num)) hrR htarget hva
  refine ⟨Ψ,?_⟩
  intro i y hy x hx
  have hm : Ψ.isotopy.map y 1 x ∈ (fun z => f i (y,z)) '' closedRoundDisk (r i) := by
    rw [←hΨ i y hy]
    exact mem_image_of_mem _ hx
  rw [himage] at hm
  obtain ⟨z,_,he⟩ := hm
  rw [←he]
  change Real.pi * radiusSq _ ∈ _
  rw [polarRoundedMap_capacity (ha i) (hb i) k (C i y) (hfit i y (hYA hy))]
  exact (hVconv y hy i).ordConnected.out ((hmargin y hy).2.1 i).1
    ((hmargin y hy).2.1 i).2 ⟨(roundedMap_mem_openBox (ha i) (hb i) k (C i y) z).1.1.le,
      (roundedMap_mem_openBox (ha i) (hb i) k (C i y) z).1.2.le⟩

end
section

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_smooth_nested_intervals_of_room {m : ℕ} {Y : Set P} (hY : IsClosed Y)
    (L : Fin m → ℝ) (hL : StrictMono L) (hpos : ∀ i, 0 < L i)
    (V : P → Fin m → Set ℝ)
    (hopen : ∀ i, IsOpen {p : P × ℝ | p.2 ∈ V p.1 i})
    (hconv : ∀ y ∈ Y, ∀ i, Convex ℝ (V y i))
    (hnest : ∀ y ∈ Y, Monotone (V y)) (hsub : ∀ y i, V y i ⊆ Ioo 0 1)
    (hroom : ∀ y ∈ Y, IntervalRoom V L y) :
    ∃ c : P → Fin m → ℝ, ContDiff ℝ ∞ c ∧
      ∀ y ∈ Y, (∀ i, Icc (c y i) (c y i+L i) ⊆ V y i) ∧ StrictNestedStarts L (c y) := by
  apply exists_smooth_nested_intervals hY L hL V
    (fun i t => (hopen i).preimage (continuous_id.prodMk continuous_const)) hconv _ hpos
  intro y hy
  have hlo (i : Fin m) : BddBelow (V y i) := ⟨0,fun x hx => (hsub y i hx).1.le⟩
  have hhi (i : Fin m) : BddAbove (V y i) := ⟨1,fun x hx => (hsub y i hx).2.le⟩
  have hne (i : Fin m) : (V y i).Nonempty := by
    obtain ⟨a,_,ha,_,_⟩ := hroom y hy i
    exact ⟨a,ha⟩
  refine ⟨fun i => sInf (V y i),fun i => sSup (V y i),?_,?_,?_,?_⟩
  · intro i j hij
    exact csInf_le_csInf (hlo j) (hne i) (hnest y hy hij)
  · intro i j hij
    exact csSup_le_csSup (hhi j) (hne i) (hnest y hy hij)
  · intro i
    obtain ⟨a,b,ha,hb,hab⟩ := hroom y hy i
    exact hab.trans_le (sub_le_sub (le_csSup (hhi i) hb) (csInf_le (hlo i) ha))
  · intro i
    exact ((hconv y hy i).isConnected (hne i)).Ioo_csInf_csSup_subset (hlo i) (hhi i)

end

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_hamiltonian_unit_grid {Y : Set P} (hY : IsCompact Y) (hcY : Convex ℝ Y)
    (y₀ : P) (hy₀ : y₀ ∈ Y) (F : C(P × ℝ,ℝ))
    (hconv : ∀ y ∈ Y, ConvexOn ℝ (Icc 0 1) (fun v => F (y,v)))
    {m : ℕ} (h : Fin m → ℝ) (hh : StrictMono h)
    (hpos : ∀ i, 0 < h i) (hbound : ∀ i, h i < 1) {ε : ℝ} (he : 0 < ε) :
    ∃ Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1), ∀ i y, y ∈ Y →
      ∀ x ∈ closedRoundDisk (areaRadius (h i)),
        F (y,radialArea (Ψ.isotopy.map y 1 x)) < unitRearrange F (y,h i)+ε := by
  let V (y : P) (i : Fin m) := unitSublevel F (h i) ε y
  have hopen : ∀ i, IsOpen {p : P × ℝ | p.2 ∈ V p.1 i} :=
    fun i => unitSublevel_open F (h i) ε
  have hsub (y : P) (i : Fin m) : V y i ⊆ Ioo 0 1 := fun _ hv => hv.1
  have hvconv (y : P) (hy : y ∈ Y) (i : Fin m) : Convex ℝ (V y i) :=
    unitSublevel_convex F y (hconv y hy) (h i) ε
  have hnest (y : P) (hy : y ∈ Y) : Monotone (V y) := by
    intro i j hij
    exact unitSublevel_mono F y (hconv y hy) ε ⟨(hpos i).le,(hbound i).le⟩
      ⟨(hpos j).le,(hbound j).le⟩ (hh.monotone hij)
  have hroom (y : P) (_ : y ∈ Y) : IntervalRoom V h y :=
    fun i => unitSublevel_room F y (hpos i).le (hbound i) he
  obtain ⟨L,w,hLmono,hwmono,hw,hrooms⟩ := exists_uniform_interval_widths hY h hh V hopen hroom
  have hLpos (i : Fin m) : 0 < L i :=
    (mul_pos_iff_of_pos_right (hw i).1).mp ((hw i).2.2 ▸ hpos i)
  obtain ⟨c,hc,hplace⟩ := exists_smooth_nested_intervals_of_room hY.isClosed
    L hLmono hLpos V hopen hvconv hnest hsub hrooms
  have hp (y : P) (hy : y ∈ Y) :
      (∀ i, c y i ∈ V y i ∧ c y i+L i ∈ V y i) ∧ StrictNestedStarts L (c y) := by
    refine ⟨fun i => ?_,(hplace y hy).2⟩
    have hle : c y i ≤ c y i+L i := le_add_of_nonneg_right (hLpos i).le
    exact ⟨(hplace y hy).1 i ⟨le_rfl,hle⟩,(hplace y hy).1 i ⟨hle,le_rfl⟩⟩
  obtain ⟨Ψ,hΨ⟩ := exists_hamiltonian_rounded_intervals hY hcY y₀ hy₀ h L w
    hpos hbound hh (fun i => (hw i).1) (fun i => (hw i).2.1) hwmono
    (fun i => (hw i).2.2) c hc V hopen hvconv hsub hp
  exact ⟨Ψ,fun i y hy x hx => (hΨ i y hy x hx).2⟩

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Comparison
open Set

theorem exists_fine_unit_grid {δ : ℝ} (hδ : 0 < δ) :
    ∃ (m : ℕ) (h : Fin m → ℝ), StrictMono h ∧ (∀ i, 0 < h i ∧ h i < 1) ∧
      ∀ v ∈ Icc (0:ℝ) 1, (∃ i, v ≤ h i ∧ h i-v < δ) ∨ 1-v < δ := by
  obtain ⟨N,hN⟩ := exists_nat_gt (1/δ)
  have hd : 0 < (N:ℝ)+1 := by positivity
  have hstep : 1/((N:ℝ)+1) < δ := (one_div_lt hd hδ).2 (by linarith)
  let h (i : Fin N) : ℝ := ((i:ℕ)+1 : ℝ)/((N:ℝ)+1)
  refine ⟨N,h,?_,?_,?_⟩
  · intro i j hij
    apply (div_lt_div_iff_of_pos_right hd).2
    have hij' : (i:ℝ) < (j:ℝ) := by exact_mod_cast hij
    change (i:ℝ)+1 < (j:ℝ)+1
    linarith
  · intro i
    constructor
    · exact div_pos (by positivity) hd
    · apply (div_lt_one hd).2
      have hi : (i:ℝ) < (N:ℝ) := by exact_mod_cast i.isLt
      change (i:ℝ)+1 < (N:ℝ)+1
      linarith
  · intro v hv
    let k := ⌊v*((N:ℝ)+1)⌋₊
    have hk : (k:ℝ) ≤ v*((N:ℝ)+1) := Nat.floor_le (mul_nonneg hv.1 hd.le)
    have hk' : v*((N:ℝ)+1) < (k:ℝ)+1 := Nat.lt_floor_add_one _
    by_cases hsmall : k < N
    · left
      refine ⟨⟨k,hsmall⟩,?_,?_⟩
      · exact ((le_div_iff₀ hd).2 hk'.le)
      · apply lt_of_le_of_lt _ hstep
        apply (le_div_iff₀ hd).2
        change (((k:ℝ)+1)/((N:ℝ)+1)-v)*((N:ℝ)+1) ≤ 1
        rw [sub_mul,div_mul_cancel₀ _ hd.ne']
        linarith
    · right
      have hNk : (N:ℝ) ≤ (k:ℝ) := by exact_mod_cast Nat.le_of_not_gt hsmall
      apply lt_of_le_of_lt _ hstep
      apply (le_div_iff₀ hd).2
      nlinarith only [hk,hNk]

variable {P : Type*} [PseudoMetricSpace P]

theorem exists_uniform_unit_modulus {Y : Set P} (hY : IsCompact Y)
    (G : C(P × ℝ,ℝ)) {ε : ℝ} (he : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ Y, ∀ u ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1,
      |u-v| < δ → G (y,u) < G (y,v)+ε := by
  have hc := (hY.prod (isCompact_Icc : IsCompact (Icc (0:ℝ) 1))).uniformContinuousOn_of_continuous
    G.continuous.continuousOn
  obtain ⟨δ,hδ,hG⟩ := Metric.uniformContinuousOn_iff.mp hc ε he
  refine ⟨δ,hδ,?_⟩
  intro y hy u hu v hv hd
  have hdist : dist (y,u) (y,v) < δ := by
    simpa only [Prod.dist_eq,dist_self,Real.dist_eq,max_eq_right (abs_nonneg (u-v))] using hd
  have hh := hG (y,u) ⟨hy,hu⟩ (y,v) ⟨hy,hv⟩ hdist
  rw [Real.dist_eq] at hh
  linarith only [(le_abs_self (G (y,u)-G (y,v))).trans_lt hh]

end PackingSufficiencySupport.Comparison

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open Comparison
open scoped BigOperators
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_hamiltonian_unit_rearrangement {Y : Set P}
    (hY : IsCompact Y) (hcY : Convex ℝ Y) (F : C(P × ℝ,ℝ))
    (hconv : ∀ y ∈ Y, ConvexOn ℝ (Icc 0 1) (fun v => F (y,v)))
    {ε : ℝ} (he : 0 < ε) :
    ∃ Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1), ∀ y ∈ Y,
      ∀ x ∈ closedRoundDisk (areaRadius 1),
        F (y,radialArea (Ψ.isotopy.map y 1 x)) ≤ unitRearrange F (y,radialArea x)+ε := by
  rcases Y.eq_empty_or_nonempty with hzero | ⟨y₀,hy₀⟩
  · refine ⟨HamiltonianDiskIsotopyFamily.refl _,?_⟩
    simp [hzero]
  have he2 : 0 < ε/2 := half_pos he
  obtain ⟨δ,hδ,hmod⟩ := exists_uniform_unit_modulus hY (unitRearrange F) he2
  obtain ⟨m,h,hh,hhi,hcover⟩ := exists_fine_unit_grid hδ
  obtain ⟨Ψ,hΨ⟩ := exists_hamiltonian_unit_grid hY hcY y₀ hy₀ F hconv h hh
    (fun i => (hhi i).1) (fun i => (hhi i).2) he2
  refine ⟨Ψ,?_⟩
  intro y hy x hx
  have hx1 : radialArea x ∈ Icc (0:ℝ) 1 :=
    ⟨radialArea_nonneg x,(mem_closedRoundDisk_areaRadius (by norm_num) x).mp hx⟩
  rcases hcover (radialArea x) hx1 with ⟨i,hle,hd⟩ | hd
  · have hxmem : x ∈ closedRoundDisk (areaRadius (h i)) :=
      (mem_closedRoundDisk_areaRadius (hhi i).1.le x).mpr hle
    have hf := hΨ i y hy x hxmem
    have hg := hmod y hy (h i) ⟨(hhi i).1.le,(hhi i).2.le⟩ (radialArea x) hx1
      (by rwa [abs_of_nonneg (sub_nonneg.mpr hle)])
    linarith
  · have hxmap := Ψ.mapsTo_closed y 1 hx
    have hm : radialArea (Ψ.isotopy.map y 1 x) ∈ Icc (0:ℝ) 1 :=
      ⟨radialArea_nonneg _,(mem_closedRoundDisk_areaRadius (by norm_num) _).mp hxmap⟩
    have hf := (hconv y hy).le_max_of_mem_Icc (show (0:ℝ) ∈ Icc 0 1 by norm_num)
      (show (1:ℝ) ∈ Icc 0 1 by norm_num) hm
    rw [←unitRearrange_one F y] at hf
    have hg := hmod y hy 1 ⟨zero_le_one,le_rfl⟩ (radialArea x) hx1
      (by rwa [abs_of_nonneg (sub_nonneg.mpr hx1.2)])
    linarith

end

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def liftArgument (j : ι) (p : ℝ × PlanePhase ι) : ((ι → ℝ) × ℝ) × Plane :=
  ((outerMoments j p.2,p.1),p.2 j)

def liftedHamiltonian (j : ι) (B : ((ι → ℝ) × ℝ) × Plane → ℝ) : ℝ × PlanePhase ι → ℝ :=
  B ∘ liftArgument j

@[fun_prop] theorem liftArgument_smooth (j : ι) : ContDiff ℝ ∞ (liftArgument j) := by
  unfold liftArgument
  exact ((outerMoments_smooth j |>.comp contDiff_snd).prodMk contDiff_fst).prodMk
    ((contDiff_apply ℝ Plane j).comp contDiff_snd)

@[fun_prop] theorem liftedHamiltonian_smooth (j : ι) {B : ((ι → ℝ) × ℝ) × Plane → ℝ}
    (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (liftedHamiltonian j B) :=
  hB.comp (liftArgument_smooth j)

theorem liftArgument_fderiv (j : ι) (p q : ℝ × PlanePhase ι) :
    fderiv ℝ (liftArgument j) p q = ((fderiv ℝ (outerMoments j) p.2 q.2,q.1),q.2 j) := by
  have hd := (((outerMoments_smooth j).differentiable (by simp) p.2).hasFDerivAt.comp p
    (hasFDerivAt_snd (𝕜 := ℝ))).prodMk (hasFDerivAt_fst (𝕜 := ℝ))
  have he := hd.prodMk ((ContinuousLinearMap.proj j : PlanePhase ι →L[ℝ] Plane).hasFDerivAt.comp p
    (hasFDerivAt_snd (𝕜 := ℝ)))
  exact congrArg (fun A : (ℝ × PlanePhase ι) →L[ℝ] _ => A q) he.fderiv

theorem liftedHamiltonian_fderiv (j : ι) {B : ((ι → ℝ) × ℝ) × Plane → ℝ}
    (hB : ContDiff ℝ ∞ B) (p q : ℝ × PlanePhase ι) :
    fderiv ℝ (liftedHamiltonian j B) p q =
      fderiv ℝ B (liftArgument j p) ((fderiv ℝ (outerMoments j) p.2 q.2,q.1),q.2 j) := by
  rw [liftedHamiltonian,fderiv_comp p (hB.differentiable (by simp) _)
    ((liftArgument_smooth j).differentiable (by simp) p)]
  rw [ContinuousLinearMap.comp_apply,liftArgument_fderiv]

omit [DecidableEq ι] in
theorem hamiltonian_slice_fderiv {B : ((ι → ℝ) × ℝ) × Plane → ℝ}
    (hB : ContDiff ℝ ∞ B) (y : ι → ℝ) (t : ℝ) (x w : Plane) :
    fderiv ℝ (fun z => B ((y,t),z)) x w = fderiv ℝ B ((y,t),x) ((0,0),w) := by
  have hd := (hB.differentiable (by simp) ((y,t),x)).hasFDerivAt.comp x
    ((hasFDerivAt_const (c := (y,t)) x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x))
  exact congrArg (fun A : Plane →L[ℝ] ℝ => A w) hd.fderiv

def liftedAngularSpeed (j i : ι) (B : ((ι → ℝ) × ℝ) × Plane → ℝ)
    (p : ℝ × PlanePhase ι) : ℝ :=
  2*Real.pi*fderiv ℝ B (liftArgument j p) ((Pi.single i 1,0),0)

@[fun_prop] theorem liftedAngularSpeed_smooth (j i : ι)
    {B : ((ι → ℝ) × ℝ) × Plane → ℝ} (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (liftedAngularSpeed j i B) := by
  exact contDiff_const.mul (((hB.fderiv_right (by simp)).comp (liftArgument_smooth j)).clm_apply
    contDiff_const)

theorem liftedHamiltonian_fderiv_inner (j : ι) {B : ((ι → ℝ) × ℝ) × Plane → ℝ}
    (hB : ContDiff ℝ ∞ B) (p : ℝ × PlanePhase ι) (w : Plane) :
    fderiv ℝ (liftedHamiltonian j B) p (0,Pi.single j w) =
      fderiv ℝ (fun z => B ((outerMoments j p.2,p.1),z)) (p.2 j) w := by
  rw [liftedHamiltonian_fderiv j hB,outerMoments_fderiv_single,hamiltonian_slice_fderiv hB]
  simp [liftArgument]

theorem liftedHamiltonian_fderiv_outer (j i : ι) (hij : i ≠ j)
    {B : ((ι → ℝ) × ℝ) × Plane → ℝ} (hB : ContDiff ℝ ∞ B)
    (p : ℝ × PlanePhase ι) (w : Plane) :
    fderiv ℝ (liftedHamiltonian j B) p (0,Pi.single i w) =
      liftedAngularSpeed j i B p*((p.2 i).1*w.1+(p.2 i).2*w.2) := by
  rw [liftedHamiltonian_fderiv j hB,outerMoments_fderiv_single]
  simp only [hij,ite_false,Pi.single_eq_of_ne (Ne.symm hij)]
  have he : (((2*Real.pi*((p.2 i).1*w.1+(p.2 i).2*w.2)) • Pi.single i (1:ℝ), (0:ℝ)), (0:Plane)) =
      (2*Real.pi*((p.2 i).1*w.1+(p.2 i).2*w.2)) • ((Pi.single i 1,0),0) := by
    simp
  rw [he,map_smul]
  dsimp [liftedAngularSpeed]
  ring

theorem liftedHamiltonian_field (j : ι) {B : ((ι → ℝ) × ℝ) × Plane → ℝ}
    (hB : ContDiff ℝ ∞ B) (p : ℝ × PlanePhase ι) (i : ι) :
    hamiltonianField phaseArea (liftedHamiltonian j B) p i =
      if i=j then planarHamiltonianField
        (fderiv ℝ (fun z => B ((outerMoments j p.2,p.1),z)) (p.2 j))
      else liftedAngularSpeed j i B p • (-(p.2 i).2,(p.2 i).1) := by
  have h₁ := hamiltonianField_contraction phaseArea_isInvertible (liftedHamiltonian j B) p
    (Pi.single i (0,1))
  have h₂ := hamiltonianField_contraction phaseArea_isInvertible (liftedHamiltonian j B) p
    (Pi.single i (1,0))
  simp only [phaseArea_single_right,planarArea_apply,mul_one,mul_zero,sub_zero,zero_sub] at h₁ h₂
  by_cases hij : i=j
  · subst i
    rw [ite_eq_left rfl]
    rw [liftedHamiltonian_fderiv_inner j hB] at h₁ h₂
    ext
    · exact h₁
    · dsimp [planarHamiltonianField]
      linarith
  · rw [ite_eq_right hij]
    rw [liftedHamiltonian_fderiv_outer j i hij hB] at h₁ h₂
    ext
    · dsimp
      nlinarith only [h₁]
    · dsimp
      nlinarith only [h₂]

end PackingSufficiencySupport.Hamiltonian
end

end OAI
