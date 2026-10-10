import OAI.Algebra.Drinfeld.Boundary

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace StraightKZ
open MeasureTheory Set Filter FinitePicard KZRectangle LogRectangle
open scoped Topology
attribute [local instance] LieRing.ofAssociativeRing
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem connection_continuousOn (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
    {X : Type*} [TopologicalSpace X] {z v : X → Fin 4 → ℝ} {S : Set X}
    (hz : ∀ i,ContinuousOn (fun x => z x i) S) (hv : ∀ i,ContinuousOn (fun x => v x i) S)
    (hn : ∀ x∈S,Function.Injective (z x)) :
    ContinuousOn (fun x => j (KZFlat.connection (z x) (v x))) S := by
  simp only [←form_eq]
  apply LogRectangle.continuousOn_form (chords j)
  · intro i
    exact (hz _).sub (hz _)
  · intro i
    exact (hv _).sub (hv _)
  · intro x hx i
    exact dif_ne_zero _ (hn x hx) i

theorem segment_connection_continuousOn (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
    {p : Fin 4 → ℝ} {q : ℝ → Fin 4 → ℝ} {a b : ℝ}
    (hp : StrictMono p) (hq : ∀ s∈Icc a b,StrictMono (q s))
    (hqc : ∀ i,ContinuousOn (fun s => q s i) (Icc a b)) :
    ContinuousOn (fun w : ℝ×ℝ => connection j p (q w.1) w.2) (Icc a b ×ˢ Icc 0 1) := by
  have hq2 (i : Fin 4) : ContinuousOn (fun w : ℝ×ℝ => q w.1 i) (Icc a b ×ˢ Icc 0 1) :=
    (hqc i).comp continuous_fst.continuousOn (fun w hw => hw.1)
  apply connection_continuousOn j
  · intro i
    exact ((continuousOn_const.sub continuous_snd.continuousOn).mul continuousOn_const).add
      (continuous_snd.continuousOn.mul (hq2 i))
  · intro i
    exact (hq2 i).sub continuousOn_const
  · intro w hw
    exact (segment_strictMono hp (hq w.1 hw.1) hw.2).injective

theorem fundamental_continuousOn (F : NilpotentFiltration A)
    (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
    {p : Fin 4 → ℝ} {q : ℝ → Fin 4 → ℝ} {a b : ℝ} (hab : a≤b)
    (hp : StrictMono p) (hq : ∀ s∈Icc a b,StrictMono (q s))
    (hqc : ∀ i,ContinuousOn (fun s => q s i) (Icc a b)) :
    ContinuousOn (fun s => fundamental F j p (q s)) (Icc a b) :=
  continuousOn_transport_parameter (Ω:=fun s t => connection j p (q s) t) (by norm_num) hab (segment_connection_continuousOn j hp hq hqc) F.cutoff

theorem fundamental_refl (F : NilpotentFiltration A)
    (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A) (p : Fin 4 → ℝ) : fundamental F j p p=1 := by
  have hh : connection j p p=(fun _ => 0) := by
    funext t
    have hv : velocity p p=0 := by ext; simp [velocity]
    simp only [connection,hv,zero_connection]
  simp only [fundamental,hh,transport,Finset.sum_range_succ',term_succ,zero_mul,
    intervalIntegral.integral_zero,Finset.sum_const_zero,term_zero,zero_add]

variable [CompleteSpace A] [FiniteDimensional ℝ A]

theorem transport_eq_ratio (F : NilpotentFiltration A)
    (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A) (hc : ∀ i,chords j i∈F.space 1)
    {p : Fin 4 → ℝ} {q q' : ℝ → Fin 4 → ℝ} {a b : ℝ} (hab : a<b)
    (hp : StrictMono p) (hq : ∀ s∈Icc a b,StrictMono (q s))
    (hqc : ∀ i,ContinuousOn (fun s => q s i) (Icc a b))
    (hqc' : ∀ i,ContinuousOn (fun s => q' s i) (Icc a b))
    (hqd : ∀ s∈Ioo a b,∀ i,HasDerivAt (fun s => q s i) (q' s i) s) :
    transport (fun s => j (KZFlat.connection (q s) (q' s))) a F.cutoff b=
      fundamental F j p (q b)*Ring.inverse (fundamental F j p (q a)) := by
  have hcon := connection_continuousOn j hqc hqc' (fun s hs => (hq s hs).injective)
  apply transport_eq_fundamental F (fun _ => connection_mem F j hc _ _) hab
    (hcon.intervalIntegrable_of_Icc hab.le) (hcon.mono Ioo_subset_Icc_self)
    (fun s hs => fundamental_derivative F j hc hp hq hqc hqc' hqd hs)
    (fundamental_continuousOn F j hab.le hp hq hqc)
    (fun s hs => fundamental_isUnit F j hc _ _)

theorem fundamental_ratio (F : NilpotentFiltration A)
    (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A) (hc : ∀ i,chords j i∈F.space 1)
    {p q r : Fin 4 → ℝ} (hp : StrictMono p) (hq : StrictMono q) (hr : StrictMono r) :
    fundamental F j q r=fundamental F j p r*Ring.inverse (fundamental F j p q) := by
  have h := transport_eq_ratio F j hc (q:=segment q r) (q':=fun _ => velocity q r)
    (by norm_num : (0:ℝ)<1) hp (fun s hs => segment_strictMono hq hr hs)
    (fun i => ((continuousOn_const.sub continuousOn_id).mul continuousOn_const).add
      (continuousOn_id.mul continuousOn_const))
    (fun i => continuousOn_const) (fun s hs i => segment_derivative q r s i)
  simpa only [segment_zero,segment_one,fundamental,connection] using! h

theorem fundamental_comp (F : NilpotentFiltration A)
    (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A) (hc : ∀ i,chords j i∈F.space 1)
    {p q r : Fin 4 → ℝ} (hp : StrictMono p) (hq : StrictMono q) (hr : StrictMono r) :
    fundamental F j q r*fundamental F j p q=fundamental F j p r := by
  rw [fundamental_ratio F j hc hp hq hr,mul_assoc,
    Ring.inverse_mul_cancel _ (fundamental_isUnit F j hc p q),mul_one]

end StraightKZ

namespace FourFrames
open MeasureTheory Set Filter FinitePicard KZCollar FourCollar KZRectangle StraightKZ
open scoped Topology
attribute [local instance] LieRing.ofAssociativeRing
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def point (x y : ℝ) : Fin 4 → ℝ := ![0,x,y,1]
def speed (vx vy : ℝ) : Fin 4 → ℝ := ![0,vx,vy,0]
def path (i : Fin 5) (s : ℝ) : Fin 4 → ℝ := point (cx i s) (cy i s)
def tangent (i : Fin 5) (s : ℝ) : Fin 4 → ℝ := speed (vx i s) (vy i s)

omit [NormedRing A] [NormedAlgebra ℝ A] in
theorem point_strictMono {x y : ℝ} (h : 0<x ∧ x<y ∧ y<1) : StrictMono (point x y) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2

omit [NormedRing A] [NormedAlgebra ℝ A] in
theorem path_strictMono (i : Fin 5) {s : ℝ} (hs : s∈Ioc 0 (1/4)) : StrictMono (path i s) :=
  point_strictMono (chamber i hs)

omit [NormedRing A] [NormedAlgebra ℝ A] in
theorem path_derivative (i : Fin 5) (s : ℝ) (k : Fin 4) :
    HasDerivAt (fun s => path i s k) (tangent i s k) s := by
  rcases coordinates_derivative i s with ⟨hx,hy⟩
  fin_cases k
  · exact hasDerivAt_const s 0
  · exact hx
  · exact hy
  · exact hasDerivAt_const s 1

omit [NormedRing A] [NormedAlgebra ℝ A] in
theorem path_continuous (i : Fin 5) (k : Fin 4) : Continuous (fun s => path i s k) :=
  continuous_iff_continuousAt.mpr (fun s => (path_derivative i s k).continuousAt)

omit [NormedRing A] [NormedAlgebra ℝ A] in
theorem tangent_continuous (i : Fin 5) (k : Fin 4) : Continuous (fun s => tangent i s k) := by
  fin_cases k
  · exact continuous_const
  · change Continuous (vx i)
    fin_cases i
    · exact continuous_const.mul continuous_id
    · exact continuous_const
    · exact continuous_const.sub (continuous_const.mul continuous_id)
    · exact continuous_const.mul continuous_id
    · exact continuous_const
  · change Continuous (vy i)
    fin_cases i
    · exact continuous_const
    · exact continuous_const.add (continuous_const.mul continuous_id)
    · exact continuous_const
    · exact continuous_const.mul continuous_id
    · exact continuous_const.mul continuous_id
  · exact continuous_const

theorem form_eq (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A) (x y vx vy : ℝ) :
    j (KZFlat.connection (point x y) (speed vx vy))=
      FourCollar.form (chords j 0) (chords j 1) (chords j 3) (chords j 4) (chords j 5) x y vx vy := by
  simp only [KZFlat.connection,KZFlat.combine,map_add,map_smul]
  change ((0-vx) / (0-x)) • j (GenericBraid.t 0 1)+((0-vy) / (0-y)) • j (GenericBraid.t 0 2)+
    ((0-0) / (0-1:ℝ)) • j (GenericBraid.t 0 3)+((vx-vy)/(x-y)) • j (GenericBraid.t 1 2)+
    ((vx-0)/(x-1)) • j (GenericBraid.t 1 3)+((vy-0)/(y-1)) • j (GenericBraid.t 2 3)=
    (vx/x) • j (GenericBraid.t 0 1)+(vy/y) • j (GenericBraid.t 0 2)+
    ((vy-vx)/(y-x)) • j (GenericBraid.t 1 2)+(vx/(x-1)) • j (GenericBraid.t 1 3)+
    (vy/(y-1)) • j (GenericBraid.t 2 3)
  simp only [zero_sub,sub_zero,neg_div_neg_eq,zero_div,zero_smul,add_zero]
  have h : (vx-vy)/(x-y)=(vy-vx)/(y-x) := by
    rw [←neg_sub vy vx,←neg_sub y x,neg_div_neg_eq]
  rw [h]

variable (F : NilpotentFiltration A) (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
  (hc : ∀ i,chords j i∈F.space 1) [CompleteSpace A] [FiniteDimensional ℝ A]

def radial (i : Fin 5) : ℝ → A :=
  normalized F (a:=chords j 0) (b:=chords j 1) (d:=chords j 3) (e:=chords j 4) (f:=chords j 5) i

include hc in
theorem radial_derivative (i : Fin 5) {s : ℝ} (hs : s∈Ioo 0 (1/4)) :
    HasDerivAt (radial F j i)
      (j (KZFlat.connection (path i s) (tangent i s))*radial F j i s) s := by
  rw [path,tangent,form_eq]
  exact normalized_derivative F (hc 0) (hc 1) (hc 3) (hc 4) (hc 5) i hs

include hc in
theorem radial_isUnit (i : Fin 5) (s : ℝ) : IsUnit (radial F j i s) :=
  normalized_isUnit F (hc 0) (hc 1) (hc 3) (hc 4) (hc 5) i s

include hc in
theorem fundamental_path_derivative {p : Fin 4 → ℝ} (hp : StrictMono p)
    (i : Fin 5) {s : ℝ} (hs : s∈Ioo 0 (1/4)) :
    HasDerivAt (fun s => fundamental F j p (path i s))
      (j (KZFlat.connection (path i s) (tangent i s))*fundamental F j p (path i s)) s := by
  apply fundamental_derivative F j hc (a:=s/2) (b:=(s+1/4)/2) hp
  · intro t ht
    apply path_strictMono i
    exact ⟨by linarith [hs.1,ht.1],by linarith [hs.2,ht.2]⟩
  · intro k
    exact (path_continuous i k).continuousOn
  · intro k
    exact (tangent_continuous i k).continuousOn
  · intro t ht k
    exact path_derivative i t k
  · exact ⟨by linarith [hs.1],by linarith [hs.2]⟩

def corner (p : Fin 4 → ℝ) (i : Fin 5) : A :=
  Ring.inverse (fundamental F j p (path i (1/8)))*radial F j i (1/8)

include hc in
theorem corner_eq {p : Fin 4 → ℝ} (hp : StrictMono p) (i : Fin 5)
    {s : ℝ} (hs : s∈Ioo 0 (1/4)) :
    Ring.inverse (fundamental F j p (path i s))*radial F j i s=corner F j p i := by
  exact transition_constant (fun t ht => fundamental_path_derivative F j hc hp i ht)
    (fun t ht => radial_derivative F j hc i ht)
    (fun _ _ => fundamental_isUnit F j hc _ _) hs (by norm_num : (1/8:ℝ)∈Ioo 0 (1/4))

include hc in
theorem corner_isUnit (p : Fin 4 → ℝ) (i : Fin 5) : IsUnit (corner F j p i) :=
by
  have hu := fundamental_isUnit F j hc p (path i (1/8))
  rw [corner,Ring.inverse_of_isUnit hu]
  exact (hu.unit⁻¹).isUnit.mul (radial_isUnit F j hc i _)

include hc in
theorem radial_eq {p : Fin 4 → ℝ} (hp : StrictMono p) (i : Fin 5)
    {s : ℝ} (hs : s∈Ioo 0 (1/4)) :
    radial F j i s=fundamental F j p (path i s)*corner F j p i := by
  rw [←corner_eq F j hc hp i hs,←mul_assoc,
    Ring.mul_inverse_cancel _ (fundamental_isUnit F j hc _ _),one_mul]

include hc in

theorem corner_cocycle (p : Fin 4 → ℝ) (i k l : Fin 5) :
    (Ring.inverse (corner F j p i)*corner F j p k)*
      (Ring.inverse (corner F j p k)*corner F j p l)=
      Ring.inverse (corner F j p i)*corner F j p l := by
  rw [mul_assoc,←mul_assoc (corner F j p k),
    Ring.mul_inverse_cancel _ (corner_isUnit F j hc p k),one_mul]

end FourFrames

section
namespace PowerAsymptotic
open Set Filter FinitePicard KZCollar Asymptotics
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

omit [NormedAlgebra ℝ A] in
theorem PowerSmall.add {f g : ℝ → A} (hf : PowerSmall f) (hg : PowerSmall g) :
    PowerSmall (fun s => f s+g s) := by
  obtain ⟨p,hp,hf⟩ := hf
  obtain ⟨q,hq,hg⟩ := hg
  have hd (u v : ℝ) (hvu : v ≤ u) :
      (fun s : ℝ => s^u) =O[𝓝[>] 0] (fun s : ℝ => s^v) := by
    apply IsBigO.of_norm_eventuallyLE
    filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with s hs
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hs.1.le _)]
    exact Real.rpow_le_rpow_of_exponent_ge hs.1 hs.2 hvu
  exact ⟨min p q,lt_min hp hq,(hf.trans (hd p _ (min_le_left _ _))).add
    (hg.trans (hd q _ (min_le_right _ _)))⟩

omit [NormedAlgebra ℝ A] in
theorem PowerSmall.subpower {f : ℝ → A} (hf : PowerSmall f) : Subpower f :=
  tendsto_subpower hf.tendsto_zero

omit [NormedAlgebra ℝ A] in
theorem subpower_of_sub {f g : ℝ → A} (hg : Subpower g)
    (hf : PowerSmall (fun s => f s-g s)) : Subpower f := by
  simpa only [sub_add_cancel] using! hf.subpower.add hg

omit [NormedAlgebra ℝ A] in
theorem frame_replacement (f l l₀ r r₀ : ℝ → A)
    (hf : Subpower f) (hl₀ : Subpower l₀) (hr₀ : Subpower r₀)
    (hl : PowerSmall (fun s => l s-l₀ s)) (hr : PowerSmall (fun s => r s-r₀ s)) :
    PowerSmall (fun s => l s*f s*r s-l₀ s*f s*r₀ s) := by
  have h := ((hl.mul_subpower hf).mul_subpower (subpower_of_sub hr₀ hr)).add
    ((hl₀.mul hf).mul_powerSmall hr)
  apply h.congr
  intro s
  simp only [sub_mul,mul_sub]
  abel

end PowerAsymptotic
namespace FourFrames
open Set Filter FinitePicard KZCollar FourCollar KZRectangle PowerAsymptotic
open scoped Topology
attribute [local instance] LieRing.ofAssociativeRing
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
variable (F : NilpotentFiltration A) (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
  (hc : ∀ i,chords j i∈F.space 1) [CompleteSpace A] [FiniteDimensional ℝ A]

def model (i : Fin 5) (s : ℝ) : A :=
  gauge (residue (chords j 0) (chords j 1) (chords j 3) (chords j 4) (chords j 5) i) s

def inverseModel (i : Fin 5) (s : ℝ) : A :=
  gauge (-residue (chords j 0) (chords j 1) (chords j 3) (chords j 4) (chords j 5) i) s

include hc in
omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem radial_error (i : Fin 5) : PowerSmall (fun s => radial F j i s-model j i s) :=
  solution_sub_gauge F (residue_mem F (hc 0) (hc 1) (hc 3) (hc 4) (hc 5) i)
    (by norm_num : (0:ℝ)<1/4) (remainder_continuous _ _ _ _ _ i)

include hc in
theorem inverse_radial_error (i : Fin 5) :
    PowerSmall (fun s => Ring.inverse (radial F j i s)-inverseModel j i s) :=
  inverse_solution_sub_gauge F (residue_mem F (hc 0) (hc 1) (hc 3) (hc 4) (hc 5) i)
    (remainder_mem F (hc 0) (hc 1) (hc 3) (hc 4) (hc 5) i)
    (by norm_num : (0:ℝ)<1/4) (remainder_continuous _ _ _ _ _ i)

include hc in
omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem model_subpower (i : Fin 5) : Subpower (model j i) :=
  gauge_subpower (pow_cutoff_eq_zero F (residue_mem F (hc 0) (hc 1) (hc 3) (hc 4) (hc 5) i))

include hc in
omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem inverseModel_subpower (i : Fin 5) : Subpower (inverseModel j i) :=
  gauge_subpower (pow_cutoff_eq_zero F ((F.space 1).neg_mem (residue_mem F (hc 0) (hc 1) (hc 3) (hc 4) (hc 5) i)))

include hc in
theorem radial_replacement (i k : Fin 5) {f : ℝ → A} (hf : Subpower f) :
    PowerSmall (fun s => Ring.inverse (radial F j k s)*f s*radial F j i s-
      inverseModel j k s*f s*model j i s) :=
  frame_replacement f _ _ _ _ hf (inverseModel_subpower F j hc k) (model_subpower F j hc i)
    (inverse_radial_error F j hc k) (radial_error F j hc i)

end FourFrames

end

namespace FourFrames
open Set Filter FinitePicard KZCollar KZRectangle StraightKZ PowerAsymptotic
open scoped Topology
attribute [local instance] LieRing.ofAssociativeRing
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
variable (F : NilpotentFiltration A) (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
  (hc : ∀ i,chords j i∈F.space 1)

include hc in
theorem normalized_transport_eq_corner {p : Fin 4 → ℝ} (hp : StrictMono p)
    (i k : Fin 5) {s : ℝ} (hs : s∈Ioo 0 (1/4)) {T : A}
    (hT : T=fundamental F j p (path k s)*Ring.inverse (fundamental F j p (path i s))) :
    Ring.inverse (radial F j k s)*T*radial F j i s=
      Ring.inverse (corner F j p k)*corner F j p i := by
  rw [hT,radial_eq F j hc hp i hs,radial_eq F j hc hp k hs,
    inverse_mul_of_units (fundamental_isUnit F j hc _ _) (corner_isUnit F j hc p k)]
  simp only [mul_assoc]
  rw [←mul_assoc (Ring.inverse (fundamental F j p (path i s))),
    Ring.inverse_mul_cancel _ (fundamental_isUnit F j hc _ _),one_mul,
    ←mul_assoc (Ring.inverse (fundamental F j p (path k s))),
    Ring.inverse_mul_cancel _ (fundamental_isUnit F j hc _ _),one_mul]

include hc in

theorem corner_eq_of_limit {p : Fin 4 → ℝ} (hp : StrictMono p) (i k : Fin 5)
    {T : ℝ → A} {v : A} (hT : Subpower T)
    (hpath : ∀ᶠ s in 𝓝[>] 0,s∈Ioo 0 (1/4) ∧
      T s=fundamental F j p (path k s)*Ring.inverse (fundamental F j p (path i s)))
    (hlim : Tendsto (fun s => inverseModel j k s*T s*model j i s) (𝓝[>] 0) (𝓝 v)) :
    Ring.inverse (corner F j p k)*corner F j p i=v := by
  have hr := (radial_replacement F j hc i k hT).tendsto_zero.add hlim
  simp only [zero_add,sub_add_cancel] at hr
  have he : (fun s => Ring.inverse (radial F j k s)*T s*radial F j i s) =ᶠ[𝓝[>] 0]
      (fun _ => Ring.inverse (corner F j p k)*corner F j p i) := by
    filter_upwards [hpath] with s hs
    exact normalized_transport_eq_corner F j hc hp i k hs.1 hs.2
  exact tendsto_nhds_unique tendsto_const_nhds (hr.congr' he)

end FourFrames

section
namespace BCBoundary
open MeasureTheory Set Filter FinitePicard KZCollar PowerAsymptotic PoleEstimate
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem bulk_subpower (X Y : A) (N : ℕ) :
    Subpower (fun s => transport (bulkForm X Y) s N (endpoint s)) := by
  apply transport_subpower (L:=mass X Y 0 0) _ (mass_subpower X Y 0 0) N
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0:ℝ)<1/4)] with s hs
  obtain ⟨hab,hb,hd⟩ := interval_bounds hs
  have hc := (bulkForm_continuous X Y).mono (show Icc s (endpoint s)⊆Ioo 0 1 from
    fun t ht => ⟨hs.1.trans_le ht.1,ht.2.trans_lt hb⟩)
  have hlog : 0 ≤ -Real.log s := neg_nonneg.mpr (Real.log_nonpos hs.1.le (by linarith [hs.2]))
  refine ⟨hab,hc.intervalIntegrable_of_Icc hab,?_,?_⟩
  · simp only [mass,norm_zero,mul_zero,zero_mul,add_zero]
    exact mul_nonneg (by positivity) hlog
  · simpa only [mass,norm_zero,mul_zero,zero_mul,add_zero] using bulk_bound X Y hs

theorem edge_subpower (X Y U V : A) (N : ℕ) :
    Subpower (fun s => transport (shiftedBulk X Y U V (s^2)) s N (endpoint s)) :=
  subpower_of_sub (bulk_subpower X Y N) (perturbation X Y U V N)

end BCBoundary
namespace FourFrames
open MeasureTheory Set Filter FinitePicard KZCollar PowerAsymptotic PoleEstimate
  KZRectangle StraightKZ BCBoundary
open scoped Topology
attribute [local instance] LieRing.ofAssociativeRing
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
variable (F : NilpotentFiltration A) (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
  (hc : ∀ i,chords j i∈F.space 1)

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem chord_triple (i k l : Fin 4) (hik : i≠k) (hil : i≠l) (hkl : k≠l) :
    Commute (j (GenericBraid.t i k)) (j (GenericBraid.t i l)+j (GenericBraid.t k l)) := by
  have h := congrArg j (GenericBraid.t_three (R:=ℝ) i k l hik hil hkl)
  rw [j.map_lie,map_add,map_zero] at h
  exact sub_eq_zero.mp h

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem BC_commute_left : Commute (chords j 3) (chords j 0+chords j 1) := by
  have h := chord_triple j 1 2 0 (by decide) (by decide) (by decide)
  rw [GenericBraid.t_comm 1 0,GenericBraid.t_comm 2 0] at h
  exact h

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem BC_commute_right : Commute (chords j 3) (chords j 4+chords j 5) :=
  chord_triple j 1 2 3 (by decide) (by decide) (by decide)

def BCtransport (s : ℝ) : A :=
  transport (shiftedBulk (chords j 0+chords j 1) (chords j 4+chords j 5)
    (chords j 1) (chords j 5) (s^2)) s F.cutoff (endpoint s)

include hc in
theorem BC_model_limit : Tendsto (fun s => inverseModel j 2 s*BCtransport F j s*model j 1 s)
    (𝓝[>] 0) (𝓝 (associator F (chords j 0+chords j 1) (chords j 4+chords j 5))) := by
  have hl := BCBoundary.limit F (chords j 1) (chords j 5)
    ((F.space 1).add_mem (hc 0) (hc 1)) ((F.space 1).add_mem (hc 4) (hc 5))
    ((F.space 1).add_mem (hc 3) (hc 3))
    ((BC_commute_left j).add_left (BC_commute_left j))
    ((BC_commute_right j).add_left (BC_commute_right j))
  convert! hl using 1
  funext s
  change KZCollar.gauge (-(chords j 5+chords j 4+2 • chords j 3)) s*BCtransport F j s*
    KZCollar.gauge (chords j 0+chords j 1+2 • chords j 3) s=
    KZCollar.gauge (-(chords j 4+chords j 5+(chords j 3+chords j 3))) s*BCtransport F j s*
    KZCollar.gauge (chords j 0+chords j 1+(chords j 3+chords j 3)) s
  rw [two_smul ℕ,add_comm (chords j 5) (chords j 4)]

include hc in
theorem BC_transport_eq {p : Fin 4 → ℝ} (hp : StrictMono p) {s : ℝ} (hs : s∈Ioo 0 (1/4)) :
    BCtransport F j s=fundamental F j p (path 2 s)*Ring.inverse (fundamental F j p (path 1 s)) := by
  let q : ℝ → Fin 4 → ℝ := fun t => point t (t+s^2)
  let q' : ℝ → Fin 4 → ℝ := fun _ => speed 1 1
  have hsq : s^2 ≤ 1/16 := by nlinarith [hs.1,hs.2,sq_nonneg (s-1/4)]
  have hab : s<endpoint s := by dsimp [endpoint]; nlinarith [hs.1,hs.2]
  have hq (t : ℝ) (ht : t∈Icc s (endpoint s)) : StrictMono (q t) := by
    apply point_strictMono
    exact ⟨hs.1.trans_le ht.1,by nlinarith [sq_pos_of_pos hs.1],by dsimp [endpoint] at ht; linarith [ht.2,hs.1]⟩
  have hqc (i : Fin 4) : ContinuousOn (fun t => q t i) (Icc s (endpoint s)) := by
    fin_cases i
    · exact continuousOn_const
    · exact continuousOn_id
    · exact continuousOn_id.add continuousOn_const
    · exact continuousOn_const
  have hqc' (i : Fin 4) : ContinuousOn (fun t => q' t i) (Icc s (endpoint s)) := continuousOn_const
  have hqd (t : ℝ) (_ : t∈Ioo s (endpoint s)) (i : Fin 4) : HasDerivAt (fun t => q t i) (q' t i) t := by
    fin_cases i
    · exact hasDerivAt_const _ _
    · exact hasDerivAt_id _
    · exact (hasDerivAt_id t).add_const (s^2)
    · exact hasDerivAt_const _ _
  have ht := transport_eq_ratio F j hc hab hp hq hqc hqc' hqd
  have hform : (fun t => j (KZFlat.connection (q t) (q' t)))=
      shiftedBulk (chords j 0+chords j 1) (chords j 4+chords j 5) (chords j 1) (chords j 5) (s^2) := by
    funext t
    rw [show q t=point t (t+s^2) from rfl,show q' t=speed 1 1 from rfl,FourFrames.form_eq,BCBoundary.form_eq]
  rw [hform] at ht
  have hqb : q (endpoint s)=path 2 s := by
    funext i
    fin_cases i <;> simp [q,path,point,FourCollar.cx,FourCollar.cy,endpoint]
  rw [hqb] at ht
  exact ht

include hc in
theorem BC_insertion {p : Fin 4 → ℝ} (hp : StrictMono p) :
    Ring.inverse (corner F j p 2)*corner F j p 1=
      associator F (chords j 0+chords j 1) (chords j 4+chords j 5) := by
  apply corner_eq_of_limit F j hc hp 1 2
    (BCBoundary.edge_subpower _ _ _ _ F.cutoff) _ (BC_model_limit F j hc)
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/4)] with s hs
  exact ⟨hs,BC_transport_eq F j hc hp hs⟩

end FourFrames

end

namespace ADBoundary
open MeasureTheory Set Filter FinitePicard KZCollar PowerAsymptotic PoleEstimate
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def endpoint (s : ℝ) : ℝ := 1-s^2

def movedPole (X Y U : A) (δ t : ℝ) : A := bulkForm X Y t+((t-δ)⁻¹-t⁻¹) • U

theorem bounds {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    s<endpoint s ∧ endpoint s<1 ∧ 2*s^2 ≤ s := by
  have hsq : s^2 ≤ 1/16 := by nlinarith [hs.1,hs.2,sq_nonneg (s-1/4)]
  unfold endpoint
  exact ⟨by nlinarith [hs.2],by nlinarith [sq_pos_of_pos hs.1],by nlinarith [hs.1,hs.2]⟩

theorem continuous (X Y U : A) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    ContinuousOn (movedPole X Y U (s^2)) (Icc s (endpoint s)) := by
  have hb := bounds hs
  have h0 := continuousOn_inv (b:=endpoint s) hs.1
  have hm : ContinuousOn (fun t : ℝ => (t-s^2)⁻¹) (Icc s (endpoint s)) :=
    (continuousOn_id.sub continuousOn_const).inv₀ (fun t ht => ne_of_gt (by change 0<t-s^2; nlinarith [hb.2.2,ht.1,hs.1]))
  have hbulk := (bulkForm_continuous X Y).mono (show Icc s (endpoint s)⊆Ioo 0 1 from
    fun t ht => ⟨hs.1.trans_le ht.1,ht.2.trans_lt hb.2.1⟩)
  exact hbulk.add ((hm.sub h0).smul continuousOn_const)

theorem error_bound (X Y U : A) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    integralNorm (fun t => movedPole X Y U (s^2) t-bulkForm X Y t) s (endpoint s) ≤ 2*‖U‖*s := by
  have hb := bounds hs
  have he : (fun t => movedPole X Y U (s^2) t-bulkForm X Y t)=
      (fun t => ((t-s^2)⁻¹-t⁻¹) • U) := by funext t; unfold movedPole; abel
  rw [he]
  calc
    _ = (∫ t in s..endpoint s,|(t-s^2)⁻¹-t⁻¹|)*‖U‖ := by
      simp only [integralNorm,norm_smul,Real.norm_eq_abs,intervalIntegral.integral_mul_const]
    _ ≤ (2*s^2*s⁻¹)*‖U‖ := mul_le_mul_of_nonneg_right
      (integral_abs_inv_sub_sub_inv_le hs.1 hb.1.le (sq_nonneg _) hb.2.2) (norm_nonneg _)
    _ = _ := by field_simp

theorem bulk_bound (X Y : A) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    integralNorm (bulkForm X Y) s (endpoint s) ≤ (‖X‖+2*‖Y‖)*(-Real.log s) := by
  have hb := bounds hs
  have h := bulkForm_mass (X:=X) (Y:=Y) hs.1 hb.1.le hb.2.1
  rw [show 1-endpoint s=s^2 by dsimp [endpoint]; ring,Real.log_pow] at h
  convert! h using 1; ring

def mass (X Y U : A) (s : ℝ) : ℝ := (‖X‖+2*‖Y‖)*(-Real.log s)+2*‖U‖*s

omit [NormedAlgebra ℝ A] in
theorem mass_subpower (X Y U : A) : Subpower (mass X Y U) := by
  have hl : Subpower (fun s : ℝ => -Real.log s) := by
    simpa only [pow_one,neg_one_mul] using (const_subpower (-1:ℝ)).mul (log_pow_subpower 1)
  exact ((const_subpower _).mul hl).add (continuousAt_subpower (continuousAt_const.mul continuousAt_id))

theorem estimates (X Y U : A) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    s ≤ endpoint s ∧ IntervalIntegrable (movedPole X Y U (s^2)) volume s (endpoint s) ∧
    IntervalIntegrable (bulkForm X Y) volume s (endpoint s) ∧
    0 ≤ mass X Y U s ∧ 0 ≤ 2*‖U‖*s ∧
    integralNorm (movedPole X Y U (s^2)) s (endpoint s) ≤ mass X Y U s ∧
    integralNorm (bulkForm X Y) s (endpoint s) ≤ mass X Y U s ∧
    integralNorm (fun t => movedPole X Y U (s^2) t-bulkForm X Y t) s (endpoint s) ≤ 2*‖U‖*s := by
  have hb := bounds hs
  have hiΩ : IntervalIntegrable (movedPole X Y U (s^2)) volume s (endpoint s) :=
    (continuous X Y U hs).intervalIntegrable_of_Icc hb.1.le
  have hiΘ : IntervalIntegrable (bulkForm X Y) volume s (endpoint s) :=
    ((bulkForm_continuous X Y).mono (show Icc s (endpoint s)⊆Ioo 0 1 from
      fun t ht => ⟨hs.1.trans_le ht.1,ht.2.trans_lt hb.2.1⟩)).intervalIntegrable_of_Icc hb.1.le
  have hE : 0 ≤ 2*‖U‖*s := mul_nonneg (by positivity) hs.1.le
  have hB : 0 ≤ (‖X‖+2*‖Y‖)*(-Real.log s) := mul_nonneg (by positivity)
    (neg_nonneg.mpr (Real.log_nonpos hs.1.le (by linarith [hs.2])))
  have hΩ : integralNorm (movedPole X Y U (s^2)) s (endpoint s) ≤ mass X Y U s := by
    have h := integralNorm_add_le hb.1.le hiΘ (hiΩ.sub hiΘ)
    have he : (fun t => bulkForm X Y t+(movedPole X Y U (s^2) t-bulkForm X Y t))=movedPole X Y U (s^2) := by funext t; abel
    rw [he] at h
    exact h.trans (add_le_add (bulk_bound X Y hs) (error_bound X Y U hs))
  exact ⟨hb.1.le,hiΩ,hiΘ,add_nonneg hB hE,hE,hΩ,
    (bulk_bound X Y hs).trans (le_add_of_nonneg_right hE),error_bound X Y U hs⟩

theorem perturbation (X Y U : A) (N : ℕ) :
    PowerSmall (fun s => transport (movedPole X Y U (s^2)) s N (endpoint s)-
      transport (bulkForm X Y) s N (endpoint s)) := by
  apply transport_perturbation_powerSmall (L:=mass X Y U) (E:=fun s => 2*‖U‖*s)
    _ (mass_subpower X Y U) (linear_powerSmall _) N
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0:ℝ)<1/4)] with s hs
  exact estimates X Y U hs

theorem transport_subpower (X Y U : A) (N : ℕ) :
    Subpower (fun s => transport (movedPole X Y U (s^2)) s N (endpoint s)) := by
  apply PowerAsymptotic.transport_subpower (L:=mass X Y U) _ (mass_subpower X Y U) N
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0:ℝ)<1/4)] with s hs
  have h := estimates X Y U hs
  exact ⟨h.1,h.2.1,h.2.2.2.1,h.2.2.2.2.2.1⟩

theorem gauge_double (X : A) (s : ℝ) : KZCollar.gauge (X+X) s=KZCollar.gauge X (s^2) := by
  unfold KZCollar.gauge
  congr 1
  rw [Real.log_pow]
  norm_num
  module

omit [NormedRing A] [NormedAlgebra ℝ A] in
theorem square_tendsto : Tendsto (fun s : ℝ => s^2) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_,?_⟩
  · simpa only [id_eq,zero_pow (by decide : 2≠0)] using
      ((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0)).pow 2)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact sq_pos_of_pos (show 0<s from hs)

variable [CompleteSpace A] [FiniteDimensional ℝ A]

theorem model_bulk_eq (F : NilpotentFiltration A) {X Y Z : A} (hZ : Z∈F.space 1)
    (hZX : Commute Z X) (hZY : Commute Z Y) (s : ℝ) :
    KZCollar.gauge (-(Z+(Y+Y))) s*transport (bulkForm X Y) s F.cutoff (endpoint s)*
      KZCollar.gauge (Z+X) s=
    KZCollar.gauge (-Y) (s^2)*transport (bulkForm X Y) s F.cutoff (1-s^2)*KZCollar.gauge X s := by
  have ht := transport_commute Z (fun t : ℝ => (hZX.smul_right (t⁻¹)).add_right (hZY.smul_right ((t-1)⁻¹))) s F.cutoff (endpoint s)
  have hg := gauge_commute (pow_cutoff_eq_zero F hZ) ht.symm s
  change Commute (transport (bulkForm X Y) s F.cutoff (endpoint s)) (KZCollar.gauge Z s) at hg
  rw [show -(Z+(Y+Y))=(-Y + -Y)+ -Z by abel,
    gauge_add_of_commute ((hZY.symm.neg_left.neg_right).add_left (hZY.symm.neg_left.neg_right)),
    gauge_double,gauge_add_of_commute hZX]
  calc
    _ = KZCollar.gauge (-Y) (s^2)*(KZCollar.gauge (-Z) s*
      (transport (bulkForm X Y) s F.cutoff (endpoint s)*KZCollar.gauge Z s))*KZCollar.gauge X s := by simp only [mul_assoc]
    _ = KZCollar.gauge (-Y) (s^2)*(KZCollar.gauge (-Z) s*
      (KZCollar.gauge Z s*transport (bulkForm X Y) s F.cutoff (endpoint s)))*KZCollar.gauge X s := by rw [hg.eq]
    _ = _ := by rw [←mul_assoc (KZCollar.gauge (-Z) s),gauge_neg_mul,one_mul]; rfl

theorem limit (F : NilpotentFiltration A) {X Y Z : A} (U : A)
    (hX : X∈F.space 1) (hY : Y∈F.space 1) (hZ : Z∈F.space 1)
    (hZX : Commute Z X) (hZY : Commute Z Y) :
    Tendsto (fun s => KZCollar.gauge (-(Z+(Y+Y))) s*
      transport (movedPole X Y U (s^2)) s F.cutoff (endpoint s)*KZCollar.gauge (Z+X) s)
      (𝓝[>] 0) (𝓝 (associator F X Y)) := by
  have hb := regularizedBulk_two_limit F hX hY tendsto_id square_tendsto
  have he (s : ℝ) := model_bulk_eq F hZ hZX hZY s
  have hb' : Tendsto (fun s => KZCollar.gauge (-(Z+(Y+Y))) s*
      transport (bulkForm X Y) s F.cutoff (endpoint s)*KZCollar.gauge (Z+X) s)
      (𝓝[>] 0) (𝓝 (associator F X Y)) := hb.congr (fun s => (he s).symm)
  have hl := normalized_perturbation_limit (perturbation X Y U F.cutoff)
    (gauge_subpower (pow_cutoff_eq_zero F ((F.space 1).neg_mem ((F.space 1).add_mem hZ ((F.space 1).add_mem hY hY)))))
    (gauge_subpower (pow_cutoff_eq_zero F ((F.space 1).add_mem hZ hX)))
  simpa only [zero_add,sub_add_cancel] using! hl.add hb'

end ADBoundary

namespace FourFrames
open MeasureTheory Set Filter FinitePicard KZCollar PowerAsymptotic PoleEstimate
  KZRectangle StraightKZ
open scoped Topology
attribute [local instance] LieRing.ofAssociativeRing
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
variable (F : NilpotentFiltration A) (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
  (hc : ∀ i,chords j i∈F.space 1)

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem AD_commute_left : Commute (chords j 0) (chords j 1+chords j 3) :=
  chord_triple j 0 1 2 (by decide) (by decide) (by decide)

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem AD_commute_right : Commute (chords j 0) (chords j 5) := by
  have h := congrArg j (GenericBraid.t_disjoint (R:=ℝ) (0:Fin 4) 1 2 3
    (by decide) (by decide) (by decide) (by decide))
  rw [j.map_lie,map_zero] at h
  exact sub_eq_zero.mp h

def ADtransport (s : ℝ) : A :=
  transport (ADBoundary.movedPole (chords j 1+chords j 3) (chords j 5) (chords j 3) (s^2))
    s F.cutoff (ADBoundary.endpoint s)

include hc in
theorem AD_model_limit : Tendsto (fun s => inverseModel j 3 s*ADtransport F j s*model j 0 s)
    (𝓝[>] 0) (𝓝 (associator F (chords j 1+chords j 3) (chords j 5))) := by
  have hl := ADBoundary.limit F (chords j 3)
    ((F.space 1).add_mem (hc 1) (hc 3)) (hc 5)
    ((F.space 1).add_mem (hc 0) (hc 0))
    ((AD_commute_left j).add_left (AD_commute_left j))
    ((AD_commute_right j).add_left (AD_commute_right j))
  convert! hl using 1
  funext s
  change KZCollar.gauge (-(2 • chords j 0+2 • chords j 5)) s*ADtransport F j s*
    KZCollar.gauge (2 • chords j 0+chords j 1+chords j 3) s=
    KZCollar.gauge (-((chords j 0+chords j 0)+(chords j 5+chords j 5))) s*ADtransport F j s*
    KZCollar.gauge ((chords j 0+chords j 0)+(chords j 1+chords j 3)) s
  simp only [two_smul ℕ,add_assoc]

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem AD_form (s t : ℝ) :
    FourCollar.form (chords j 0) (chords j 1) (chords j 3) (chords j 4) (chords j 5)
      (s^2) t 0 1=ADBoundary.movedPole (chords j 1+chords j 3) (chords j 5) (chords j 3) (s^2) t := by
  simp only [FourCollar.form,ADBoundary.movedPole,bulkForm,one_div,sub_zero,zero_div,zero_smul,zero_add,add_zero,
    smul_add,sub_smul]
  abel

include hc in
theorem AD_transport_eq {p : Fin 4 → ℝ} (hp : StrictMono p) {s : ℝ} (hs : s∈Ioo 0 (1/4)) :
    ADtransport F j s=fundamental F j p (path 3 s)*Ring.inverse (fundamental F j p (path 0 s)) := by
  let q : ℝ → Fin 4 → ℝ := fun t => point (s^2) t
  let q' : ℝ → Fin 4 → ℝ := fun _ => speed 0 1
  have hb := ADBoundary.bounds ⟨hs.1,hs.2.le⟩
  have hq (t : ℝ) (ht : t∈Icc s (ADBoundary.endpoint s)) : StrictMono (q t) := by
    apply point_strictMono
    exact ⟨sq_pos_of_pos hs.1,by nlinarith [hb.2.2,ht.1,hs.1],ht.2.trans_lt hb.2.1⟩
  have hqc (i : Fin 4) : ContinuousOn (fun t => q t i) (Icc s (ADBoundary.endpoint s)) := by
    fin_cases i
    · exact continuousOn_const
    · exact continuousOn_const
    · exact continuousOn_id
    · exact continuousOn_const
  have hqc' (i : Fin 4) : ContinuousOn (fun t => q' t i) (Icc s (ADBoundary.endpoint s)) := continuousOn_const
  have hqd (t : ℝ) (_ : t∈Ioo s (ADBoundary.endpoint s)) (i : Fin 4) : HasDerivAt (fun t => q t i) (q' t i) t := by
    fin_cases i
    · exact hasDerivAt_const _ _
    · exact hasDerivAt_const _ _
    · exact hasDerivAt_id _
    · exact hasDerivAt_const _ _
  have ht := transport_eq_ratio F j hc hb.1 hp hq hqc hqc' hqd
  have hform : (fun t => j (KZFlat.connection (q t) (q' t)))=
      ADBoundary.movedPole (chords j 1+chords j 3) (chords j 5) (chords j 3) (s^2) := by
    funext t
    rw [show q t=point (s^2) t from rfl,show q' t=speed 0 1 from rfl,FourFrames.form_eq,AD_form]
  rw [hform] at ht
  exact ht

include hc in
theorem AD_insertion {p : Fin 4 → ℝ} (hp : StrictMono p) :
    Ring.inverse (corner F j p 3)*corner F j p 0=
      associator F (chords j 1+chords j 3) (chords j 5) := by
  apply corner_eq_of_limit F j hc hp 0 3
    (ADBoundary.transport_subpower _ _ _ F.cutoff) _ (AD_model_limit F j hc)
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/4)] with s hs
  exact ⟨hs,AD_transport_eq F j hc hp hs⟩

end FourFrames

namespace ABBoundary

section
open Set Filter
open scoped Topology

def endpoint (s : ℝ) : ℝ := (1+s)⁻¹
def slope (s : ℝ) : ℝ := s^2/(endpoint s-s)
def scale (s t : ℝ) : ℝ := s+slope s*(t-s)
def scaleV (s t : ℝ) : ℝ := scale s t+t*slope s

theorem endpoint_bounds {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    1/2 ≤ endpoint s-s ∧ endpoint s<1 ∧ s<endpoint s := by
  have hp : 0<1+s := by linarith [hs.1]
  have hlo : 3/4 ≤ endpoint s := by
    rw [endpoint,←one_div]
    rw [le_div_iff₀ hp]
    nlinarith [hs.2]
  have hup : endpoint s<1 := by
    rw [endpoint,inv_lt_one₀ hp]
    linarith [hs.1]
  exact ⟨by linarith [hs.2],hup,by linarith [hs.2]⟩

theorem slope_bounds {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    0≤ slope s ∧ slope s≤ 2*s^2 := by
  have hb := endpoint_bounds hs
  have hp : 0<endpoint s-s := by linarith [hb.1]
  constructor
  · exact div_nonneg (sq_nonneg _) hp.le
  · rw [slope,div_le_iff₀ hp]
    nlinarith [sq_nonneg s]

theorem scale_start (s : ℝ) : scale s s=s := by simp [scale]

theorem scale_end {s : ℝ} (hs : s∈Ioc 0 (1/4)) : scale s (endpoint s)=s+s^2 := by
  unfold scale slope
  rw [div_mul_cancel₀ _ (sub_ne_zero.mpr (endpoint_bounds hs).2.2.ne')]

theorem endpoint_mul_scale {s : ℝ} (hs : s∈Ioc 0 (1/4)) : endpoint s*scale s (endpoint s)=s := by
  rw [scale_end hs,endpoint]
  have h : 1+s≠0 := by linarith [hs.1]
  field_simp

theorem scale_bounds {s t : ℝ} (hs : s∈Ioc 0 (1/4)) (ht : t∈Icc s (endpoint s)) :
    s≤ scale s t ∧ scale s t≤ s+s^2 ∧ scale s t≤ 1/2 ∧ 0≤ t ∧ t≤ 1 := by
  have hc := slope_bounds hs
  have hlow : s≤ scale s t := le_add_of_nonneg_right (mul_nonneg hc.1 (sub_nonneg.mpr ht.1))
  have hhigh : scale s t≤ s+s^2 := by
    rw [←scale_end hs]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 s) hc.1)
  have hsq : s^2≤ 1/16 := by nlinarith [hs.1,hs.2,sq_nonneg (s-1/4)]
  exact ⟨hlow,hhigh,by linarith [hs.2],hs.1.le.trans ht.1,ht.2.trans (endpoint_bounds hs).2.1.le⟩

theorem velocity_bounds {s t : ℝ} (hs : s∈Ioc 0 (1/4)) (ht : t∈Icc s (endpoint s)) :
    0≤ scaleV s t ∧ scaleV s t≤ 2*s := by
  have hb := scale_bounds hs ht
  have hc := slope_bounds hs
  unfold scaleV
  constructor
  · exact add_nonneg (hs.1.le.trans hb.1) (mul_nonneg hb.2.2.2.1 hc.1)
  · have hm := mul_le_mul_of_nonneg_right hb.2.2.2.2 hc.1
    nlinarith [hs.1,hs.2]

theorem coefficient_bounds {s t : ℝ} (hs : s∈Ioc 0 (1/4)) (ht : t∈Icc s (endpoint s)) :
    |slope s/scale s t|≤ 2*s ∧ |scaleV s t/(t*scale s t-1)|≤ 4*s ∧
    |slope s/(scale s t-1)|≤ 4*s := by
  have hb := scale_bounds hs ht
  have hc := slope_bounds hs
  have hv := velocity_bounds hs ht
  have hy : 0<scale s t := hs.1.trans_le hb.1
  have hxy : t*scale s t≤ 1/2 := (mul_le_of_le_one_left hy.le hb.2.2.2.2).trans hb.2.2.1
  constructor
  · rw [abs_of_nonneg (div_nonneg hc.1 hy.le),div_le_iff₀ hy]
    nlinarith [mul_le_mul_of_nonneg_left hb.1 hs.1.le]
  constructor
  · rw [abs_div,abs_of_nonneg hv.1,abs_of_nonpos (by linarith : t*scale s t-1≤ 0)]
    rw [div_le_iff₀ (by linarith : 0< -(t*scale s t-1))]
    nlinarith [mul_le_mul_of_nonneg_left hxy hs.1.le]
  · rw [abs_div,abs_of_nonneg hc.1,abs_of_nonpos (by linarith [hb.2.2.1] : scale s t-1≤ 0)]
    rw [div_le_iff₀ (by linarith [hb.2.2.1] : 0< -(scale s t-1))]
    nlinarith [mul_le_mul_of_nonneg_left hb.2.2.1 hs.1.le,hs.2,hs.1]

theorem chamber {s t : ℝ} (hs : s∈Ioc 0 (1/4)) (ht : t∈Icc s (endpoint s)) :
    0<t*scale s t ∧ t*scale s t<scale s t ∧ scale s t<1 := by
  have hb := scale_bounds hs ht
  have hy := hs.1.trans_le hb.1
  exact ⟨mul_pos (hs.1.trans_le ht.1) hy,mul_lt_of_lt_one_left hy (ht.2.trans_lt (endpoint_bounds hs).2.1),
    lt_of_le_of_lt hb.2.2.1 (by norm_num)⟩

theorem scale_deriv (s t : ℝ) : HasDerivAt (scale s) (slope s) t := by
  simpa only [scale,id_eq,mul_one] using! ((hasDerivAt_id t).sub_const s).const_mul (slope s) |>.const_add s

theorem x_deriv (s t : ℝ) : HasDerivAt (fun t => t*scale s t) (scaleV s t) t := by
  simpa only [scaleV,Pi.mul_apply,id_eq,one_mul] using! (hasDerivAt_id t).mul (scale_deriv s t)

theorem scale_continuous (s : ℝ) : Continuous (scale s) :=
  continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const))

theorem form_eq {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (a b d e f : A) {s t : ℝ} (hs : s∈Ioc 0 (1/4)) (ht : t∈Icc s (endpoint s)) :
    FourCollar.form a b d e f (t*scale s t) (scale s t) (scaleV s t) (slope s)=
      KZCollar.bulkForm a d t+(slope s/scale s t) • (a+b+d)+
        (scaleV s t/(t*scale s t-1)) • e+(slope s/(scale s t-1)) • f := by
  have hb := scale_bounds hs ht
  have ht0 : t≠0 := ne_of_gt (hs.1.trans_le ht.1)
  have hy : scale s t≠0 := ne_of_gt (hs.1.trans_le hb.1)
  have ht1 : t-1≠0 := ne_of_lt (sub_neg.mpr (ht.2.trans_lt (endpoint_bounds hs).2.1))
  have hxy : scale s t-t*scale s t≠0 := ne_of_gt (sub_pos.mpr (chamber hs ht).2.1)
  have h1t : 1-t≠0 := ne_of_gt (sub_pos.mpr (ht.2.trans_lt (endpoint_bounds hs).2.1))
  unfold FourCollar.form KZCollar.bulkForm scaleV
  match_scalars <;> field_simp [ht0,hy,ht1,hxy,h1t]
  ring

end

section
open MeasureTheory Set Filter FinitePicard KZCollar PowerAsymptotic PoleEstimate
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def error (S E V : A) (s t : ℝ) : A :=
  (slope s/scale s t) • S+(scaleV s t/(t*scale s t-1)) • E+(slope s/(scale s t-1)) • V

def edgeForm (X Y S E V : A) (s t : ℝ) : A := bulkForm X Y t+error S E V s t

def errorConst (S E V : A) : ℝ := 2*‖S‖+4*‖E‖+4*‖V‖

omit [NormedAlgebra ℝ A] in
theorem errorConst_nonneg (S E V : A) : 0 ≤ errorConst S E V := by unfold errorConst; positivity

theorem error_norm (S E V : A) {s t : ℝ} (hs : s∈Ioc 0 (1/4)) (ht : t∈Icc s (endpoint s)) :
    ‖error S E V s t‖ ≤ errorConst S E V*s := by
  have hb := coefficient_bounds hs ht
  calc
    _ ≤ ‖(slope s/scale s t) • S‖+‖(scaleV s t/(t*scale s t-1)) • E‖+‖(slope s/(scale s t-1)) • V‖ := norm_add₃_le
    _ ≤ (2*s)*‖S‖+(4*s)*‖E‖+(4*s)*‖V‖ := by
      simp only [norm_smul,Real.norm_eq_abs]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hb.1 (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hb.2.1 (norm_nonneg _)))
        (mul_le_mul_of_nonneg_right hb.2.2 (norm_nonneg _))
    _ = _ := by unfold errorConst; ring

theorem error_continuous (S E V : A) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    ContinuousOn (error S E V s) (Icc s (endpoint s)) := by
  have hy := (scale_continuous s).continuousOn (s:=Icc s (endpoint s))
  have hv : ContinuousOn (scaleV s) (Icc s (endpoint s)) := hy.add (continuousOn_id.mul continuousOn_const)
  have hm := (continuousOn_id.mul hy).sub (continuousOn_const (c:=(1:ℝ)))
  have hy0 : ∀ t∈Icc s (endpoint s),scale s t≠0 := fun t ht => ne_of_gt (hs.1.trans_le (scale_bounds hs ht).1)
  have hm0 : ∀ t∈Icc s (endpoint s),t*scale s t-1≠0 := fun t ht => ne_of_lt (by
    have h := chamber hs ht; linarith [h.2.1,h.2.2])
  have hy1 : ∀ t∈Icc s (endpoint s),scale s t-1≠0 := fun t ht => ne_of_lt (by linarith [(chamber hs ht).2.2])
  exact (((continuousOn_const.div hy hy0).smul continuousOn_const).add
    ((hv.div hm hm0).smul continuousOn_const)).add
      ((continuousOn_const.div (hy.sub continuousOn_const) hy1).smul continuousOn_const)

theorem bulk_continuous (X Y : A) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    ContinuousOn (bulkForm X Y) (Icc s (endpoint s)) :=
  (bulkForm_continuous X Y).mono (fun _ ht => ⟨hs.1.trans_le ht.1,ht.2.trans_lt (endpoint_bounds hs).2.1⟩)

theorem continuous (X Y S E V : A) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    ContinuousOn (edgeForm X Y S E V s) (Icc s (endpoint s)) :=
  (bulk_continuous X Y hs).add (error_continuous S E V hs)

theorem error_bound (X Y S E V : A) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    integralNorm (fun t => edgeForm X Y S E V s t-bulkForm X Y t) s (endpoint s) ≤ errorConst S E V*s := by
  simp only [edgeForm,add_sub_cancel_left]
  have hb := endpoint_bounds hs
  have hi : IntervalIntegrable (error S E V s) volume s (endpoint s) :=
    (error_continuous S E V hs).intervalIntegrable_of_Icc hb.2.2.le
  calc
    _ ≤ ∫ _ in s..endpoint s,errorConst S E V*s :=
      intervalIntegral.integral_mono_on hb.2.2.le hi.norm intervalIntegrable_const (fun t ht => error_norm S E V hs ht)
    _ = (endpoint s-s)*(errorConst S E V*s) := by rw [intervalIntegral.integral_const,smul_eq_mul]
    _ ≤ _ := mul_le_of_le_one_left (mul_nonneg (errorConst_nonneg S E V) hs.1.le)
      (by linarith [hb.2.1,hs.1])

def mass (X Y S E V : A) (s : ℝ) : ℝ :=
  (‖X‖+‖Y‖)*(-Real.log s)+‖Y‖*Real.log 2+errorConst S E V*s

theorem gap_eq {s : ℝ} (hs : 0<s) : 1-endpoint s=s/(1+s) := by
  unfold endpoint
  field_simp
  ring

theorem gap_bound {s : ℝ} (hs : s∈Ioc 0 (1/4)) : s/2 ≤ 1-endpoint s := by
  rw [gap_eq hs.1]
  have hp : 0<1+s := by linarith [hs.1]
  rw [le_div_iff₀ hp]
  nlinarith [hs.1,hs.2]

theorem bulk_bound (X Y : A) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    integralNorm (bulkForm X Y) s (endpoint s) ≤ (‖X‖+‖Y‖)*(-Real.log s)+‖Y‖*Real.log 2 := by
  have hb := endpoint_bounds hs
  have hl : -Real.log (1-endpoint s) ≤ -Real.log s+Real.log 2 := by
    have h := Real.log_le_log (by linarith [hs.1] : 0<s/2) (gap_bound hs)
    rw [Real.log_div hs.1.ne' (by norm_num)] at h
    linarith
  calc
    _ ≤ ‖X‖*(-Real.log s)+‖Y‖*(-Real.log (1-endpoint s)) := bulkForm_mass hs.1 hb.2.2.le hb.2.1
    _ ≤ ‖X‖*(-Real.log s)+‖Y‖*(-Real.log s+Real.log 2) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hl (norm_nonneg _))
    _ = _ := by ring

omit [NormedAlgebra ℝ A] in
theorem mass_subpower (X Y S E V : A) : Subpower (mass X Y S E V) := by
  have hl : Subpower (fun s : ℝ => -Real.log s) := by
    simpa only [pow_one,neg_one_mul] using (const_subpower (-1:ℝ)).mul (log_pow_subpower 1)
  exact (((const_subpower _).mul hl).add (const_subpower _)).add
    (continuousAt_subpower (continuousAt_const.mul continuousAt_id))

theorem estimates (X Y S E V : A) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    s ≤ endpoint s ∧ IntervalIntegrable (edgeForm X Y S E V s) volume s (endpoint s) ∧
      IntervalIntegrable (bulkForm X Y) volume s (endpoint s) ∧ 0 ≤ mass X Y S E V s ∧
      0 ≤ errorConst S E V*s ∧ integralNorm (edgeForm X Y S E V s) s (endpoint s) ≤ mass X Y S E V s ∧
      integralNorm (bulkForm X Y) s (endpoint s) ≤ mass X Y S E V s ∧
      integralNorm (fun t => edgeForm X Y S E V s t-bulkForm X Y t) s (endpoint s) ≤ errorConst S E V*s := by
  have hb := endpoint_bounds hs
  have hiΩ : IntervalIntegrable (edgeForm X Y S E V s) volume s (endpoint s) := (continuous X Y S E V hs).intervalIntegrable_of_Icc hb.2.2.le
  have hiΘ : IntervalIntegrable (bulkForm X Y) volume s (endpoint s) := (bulk_continuous X Y hs).intervalIntegrable_of_Icc hb.2.2.le
  have hE : 0 ≤ errorConst S E V*s := mul_nonneg (errorConst_nonneg S E V) hs.1.le
  have hl : 0 ≤ -Real.log s := neg_nonneg.mpr (Real.log_nonpos hs.1.le (by linarith [hs.2]))
  have hL : 0 ≤ mass X Y S E V s := add_nonneg (add_nonneg (mul_nonneg (by positivity) hl)
    (mul_nonneg (norm_nonneg _) (Real.log_nonneg (by norm_num)))) hE
  have hΩ : integralNorm (edgeForm X Y S E V s) s (endpoint s) ≤ mass X Y S E V s := by
    have h := integralNorm_add_le hb.2.2.le hiΘ (hiΩ.sub hiΘ)
    have he : (fun t => bulkForm X Y t+(edgeForm X Y S E V s t-bulkForm X Y t))=edgeForm X Y S E V s := by funext t; abel
    rw [he] at h
    exact h.trans (add_le_add (bulk_bound X Y hs) (error_bound X Y S E V hs))
  exact ⟨hb.2.2.le,hiΩ,hiΘ,hL,hE,hΩ,(bulk_bound X Y hs).trans (le_add_of_nonneg_right hE),error_bound X Y S E V hs⟩

theorem perturbation (X Y S E V : A) (N : ℕ) :
    PowerSmall (fun s => transport (edgeForm X Y S E V s) s N (endpoint s)-transport (bulkForm X Y) s N (endpoint s)) := by
  apply transport_perturbation_powerSmall (L:=mass X Y S E V) (E:=fun s => errorConst S E V*s)
    _ (mass_subpower X Y S E V) (linear_powerSmall _) N
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0:ℝ)<1/4)] with s hs
  exact estimates X Y S E V hs

theorem transport_subpower (X Y S E V : A) (N : ℕ) :
    Subpower (fun s => transport (edgeForm X Y S E V s) s N (endpoint s)) := by
  apply PowerAsymptotic.transport_subpower (L:=mass X Y S E V) _ (mass_subpower X Y S E V) N
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0:ℝ)<1/4)] with s hs
  have h := estimates X Y S E V hs
  exact ⟨h.1,h.2.1,h.2.2.2.1,h.2.2.2.2.2.1⟩

end

open Set Filter FinitePicard KZCollar PowerAsymptotic
open scoped Topology

theorem gap_tendsto : Tendsto (fun s : ℝ => s/(1+s)) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [add_zero,zero_div] using! h.div (tendsto_const_nhds.add h) (by norm_num : (1:ℝ)+0≠0)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    change 0<s at hs
    exact div_pos hs (by linarith)

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]

theorem bulk_limit (F : NilpotentFiltration A) {X Y : A}
    (hX : X∈F.space 1) (hY : Y∈F.space 1) :
    Tendsto (fun s => gauge (-Y) s*transport (bulkForm X Y) s F.cutoff (endpoint s)*gauge X s)
      (𝓝[>] 0) (𝓝 (associator F X Y)) := by
  have h := (gauge_ratio_limit (-Y)).mul (regularizedBulk_two_limit F hX hY tendsto_id gap_tendsto)
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  change 0<s at hs
  have hp : 0<1+s := by linarith
  have hg : gauge (-Y) (1+s)*gauge (-Y) (s/(1+s))=gauge (-Y) s := by
    rw [←gauge_mul_scale _ hp.ne' (ne_of_gt (div_pos hs hp)),mul_div_cancel₀ _ hp.ne']
  simp only [←mul_assoc]
  rw [hg,show 1-s/(1+s)=endpoint s by have he := gap_eq hs; linarith]
  rfl

theorem limit (F : NilpotentFiltration A) {X Y Z : A} (S E V : A)
    (hX : X∈F.space 1) (hY : Y∈F.space 1) (hZ : Z∈F.space 1)
    (hZX : Commute Z X) (hZY : Commute Z Y) :
    Tendsto (fun s => gauge (-(Y+Z)) s*transport (edgeForm X Y S E V s) s F.cutoff (endpoint s)*gauge (X+Z) s)
      (𝓝[>] 0) (𝓝 (associator F X Y)) := by
  have hl := normalized_perturbation_limit (perturbation X Y S E V F.cutoff)
    (gauge_subpower (pow_cutoff_eq_zero F ((F.space 1).neg_mem ((F.space 1).add_mem hY hZ))))
    (gauge_subpower (pow_cutoff_eq_zero F ((F.space 1).add_mem hX hZ)))
  have he (s : ℝ) := BCBoundary.shared_residue_cancel (pow_cutoff_eq_zero F hZ) hZX hZY s (endpoint s) s
  have hb : Tendsto (fun s => gauge (-(Y+Z)) s*transport (bulkForm X Y) s F.cutoff (endpoint s)*gauge (X+Z) s)
      (𝓝[>] 0) (𝓝 (associator F X Y)) := (bulk_limit F hX hY).congr (fun s => (he s).symm)
  simpa only [zero_add,sub_add_cancel] using! hl.add hb

end ABBoundary

namespace FourFrames

section
open MeasureTheory Set Filter FinitePicard KZCollar PowerAsymptotic PoleEstimate
  KZRectangle StraightKZ
open scoped Topology
attribute [local instance] LieRing.ofAssociativeRing
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
variable (F : NilpotentFiltration A) (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
  (hc : ∀ i,chords j i∈F.space 1)

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem AB_commute_left : Commute (chords j 0+chords j 1+chords j 3) (chords j 0) := by
  rw [add_assoc]
  exact (Commute.refl _).add_left (AD_commute_left j).symm

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem AB_commute_right : Commute (chords j 0+chords j 1+chords j 3) (chords j 3) :=
  (BC_commute_left j).symm.add_left (Commute.refl _)

def ABtransport (s : ℝ) : A :=
  transport (ABBoundary.edgeForm (chords j 0) (chords j 3) (chords j 0+chords j 1+chords j 3)
    (chords j 4) (chords j 5) s) s F.cutoff (ABBoundary.endpoint s)

include hc in
theorem AB_model_limit : Tendsto (fun s => inverseModel j 1 s*ABtransport F j s*model j 0 s)
    (𝓝[>] 0) (𝓝 (associator F (chords j 0) (chords j 3))) := by
  have hl := ABBoundary.limit F (chords j 0+chords j 1+chords j 3) (chords j 4) (chords j 5)
    (hc 0) (hc 3) ((F.space 1).add_mem ((F.space 1).add_mem (hc 0) (hc 1)) (hc 3))
    (AB_commute_left j) (AB_commute_right j)
  convert! hl using 1
  funext s
  change KZCollar.gauge (-(chords j 0+chords j 1+2 • chords j 3)) s*ABtransport F j s*
    KZCollar.gauge (2 • chords j 0+chords j 1+chords j 3) s=
    KZCollar.gauge (-(chords j 3+(chords j 0+chords j 1+chords j 3))) s*ABtransport F j s*
    KZCollar.gauge (chords j 0+(chords j 0+chords j 1+chords j 3)) s
  rw [two_smul ℕ,two_smul ℕ,show chords j 0+chords j 1+(chords j 3+chords j 3)=
    chords j 3+(chords j 0+chords j 1+chords j 3) by abel]
  simp only [add_assoc]

include hc in
theorem AB_transport_eq {p : Fin 4 → ℝ} (hp : StrictMono p) {s : ℝ} (hs : s∈Ioo 0 (1/4)) :
    ABtransport F j s=fundamental F j p (path 1 s)*Ring.inverse (fundamental F j p (path 0 s)) := by
  let q : ℝ → Fin 4 → ℝ := fun t => point (t*ABBoundary.scale s t) (ABBoundary.scale s t)
  let q' : ℝ → Fin 4 → ℝ := fun t => speed (ABBoundary.scaleV s t) (ABBoundary.slope s)
  have hb := ABBoundary.endpoint_bounds ⟨hs.1,hs.2.le⟩
  have hq (t : ℝ) (ht : t∈Icc s (ABBoundary.endpoint s)) : StrictMono (q t) :=
    point_strictMono (ABBoundary.chamber ⟨hs.1,hs.2.le⟩ ht)
  have hqc (i : Fin 4) : ContinuousOn (fun t => q t i) (Icc s (ABBoundary.endpoint s)) := by
    fin_cases i
    · exact continuousOn_const
    · exact (continuous_id.mul (ABBoundary.scale_continuous s)).continuousOn
    · exact (ABBoundary.scale_continuous s).continuousOn
    · exact continuousOn_const
  have hqc' (i : Fin 4) : ContinuousOn (fun t => q' t i) (Icc s (ABBoundary.endpoint s)) := by
    fin_cases i
    · exact continuousOn_const
    · exact ((ABBoundary.scale_continuous s).add (continuous_id.mul continuous_const)).continuousOn
    · exact continuousOn_const
    · exact continuousOn_const
  have hqd (t : ℝ) (_ : t∈Ioo s (ABBoundary.endpoint s)) (i : Fin 4) : HasDerivAt (fun t => q t i) (q' t i) t := by
    fin_cases i
    · exact hasDerivAt_const _ _
    · exact ABBoundary.x_deriv s t
    · exact ABBoundary.scale_deriv s t
    · exact hasDerivAt_const _ _
  have ht := transport_eq_ratio F j hc hb.2.2 hp hq hqc hqc' hqd
  have hform : Set.EqOn (fun t => j (KZFlat.connection (q t) (q' t)))
      (ABBoundary.edgeForm (chords j 0) (chords j 3) (chords j 0+chords j 1+chords j 3)
        (chords j 4) (chords j 5) s) (Icc s (ABBoundary.endpoint s)) := by
    intro t hti
    dsimp only
    rw [show q t=point (t*ABBoundary.scale s t) (ABBoundary.scale s t) from rfl,
      show q' t=speed (ABBoundary.scaleV s t) (ABBoundary.slope s) from rfl,FourFrames.form_eq,
      ABBoundary.form_eq _ _ _ _ _ ⟨hs.1,hs.2.le⟩ hti]
    simp only [ABBoundary.edgeForm,ABBoundary.error,add_assoc]
  have he := transport_congr (a:=s) (b:=ABBoundary.endpoint s) (by simpa only [uIcc_of_le hb.2.2.le] using hform) F.cutoff
  rw [he] at ht
  have hqb : q (ABBoundary.endpoint s)=path 1 s := by
    funext i
    fin_cases i <;> simp [q,path,point,FourCollar.cx,FourCollar.cy,ABBoundary.scale_end ⟨hs.1,hs.2.le⟩]
    have he := ABBoundary.endpoint_mul_scale ⟨hs.1,hs.2.le⟩
    rw [ABBoundary.scale_end ⟨hs.1,hs.2.le⟩] at he
    exact he
  have hqa : q s=path 0 s := by
    funext i
    fin_cases i <;> simp [q,path,point,FourCollar.cx,FourCollar.cy,ABBoundary.scale_start,pow_two]
  rw [hqa,hqb] at ht
  exact ht

include hc in
theorem AB_insertion {p : Fin 4 → ℝ} (hp : StrictMono p) :
    Ring.inverse (corner F j p 1)*corner F j p 0=associator F (chords j 0) (chords j 3) := by
  apply corner_eq_of_limit F j hc hp 0 1
    (ABBoundary.transport_subpower _ _ _ _ _ F.cutoff) _ (AB_model_limit F j hc)
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/4)] with s hs
  exact ⟨hs,AB_transport_eq F j hc hp hs⟩

end

section
open MeasureTheory Set Filter FinitePicard KZCollar PowerAsymptotic PoleEstimate
  KZRectangle StraightKZ
open scoped Topology
attribute [local instance] LieRing.ofAssociativeRing
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
variable (F : NilpotentFiltration A) (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
  (hc : ∀ i,chords j i∈F.space 1)

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem ED_commute_left : Commute (chords j 5) (chords j 4+chords j 3) := by
  have h := chord_triple j 2 3 1 (by decide) (by decide) (by decide)
  rw [GenericBraid.t_comm 2 1,GenericBraid.t_comm 3 1,add_comm] at h
  exact h

def EDtransport (s : ℝ) : A :=
  transport (ADBoundary.movedPole (chords j 4+chords j 3) (chords j 0) (chords j 3) (s^2))
    s F.cutoff (ADBoundary.endpoint s)

include hc in
theorem ED_model_limit : Tendsto (fun s => inverseModel j 3 s*EDtransport F j s*model j 4 s)
    (𝓝[>] 0) (𝓝 (associator F (chords j 4+chords j 3) (chords j 0))) := by
  have hl := ADBoundary.limit F (chords j 3)
    ((F.space 1).add_mem (hc 4) (hc 3)) (hc 0)
    ((F.space 1).add_mem (hc 5) (hc 5))
    ((ED_commute_left j).add_left (ED_commute_left j))
    ((AD_commute_right j).symm.add_left (AD_commute_right j).symm)
  convert! hl using 1
  funext s
  change KZCollar.gauge (-(2 • chords j 0+2 • chords j 5)) s*EDtransport F j s*
    KZCollar.gauge (2 • chords j 5+chords j 4+chords j 3) s=
    KZCollar.gauge (-((chords j 5+chords j 5)+(chords j 0+chords j 0))) s*EDtransport F j s*
    KZCollar.gauge ((chords j 5+chords j 5)+(chords j 4+chords j 3)) s
  rw [add_comm (2 • chords j 0) (2 • chords j 5)]
  simp only [two_smul ℕ,add_assoc]

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem ED_form (s t : ℝ) :
    FourCollar.form (chords j 0) (chords j 1) (chords j 3) (chords j 4) (chords j 5)
      (1-t) (1-s^2) (-1) 0=
      ADBoundary.movedPole (chords j 4+chords j 3) (chords j 0) (chords j 3) (s^2) t := by
  unfold FourCollar.form ADBoundary.movedPole bulkForm
  rw [show 1-s^2-(1-t)=t-s^2 by ring,show 1-t-1= -t by ring,
    show 1-t= -(t-1) by ring]
  simp only [zero_div,zero_smul,add_zero,zero_sub,neg_neg,neg_div_neg_eq,one_div,
    smul_add,sub_smul]
  abel

include hc in
theorem ED_transport_eq {p : Fin 4 → ℝ} (hp : StrictMono p) {s : ℝ} (hs : s∈Ioo 0 (1/4)) :
    EDtransport F j s=fundamental F j p (path 3 s)*Ring.inverse (fundamental F j p (path 4 s)) := by
  let q : ℝ → Fin 4 → ℝ := fun t => point (1-t) (1-s^2)
  let q' : ℝ → Fin 4 → ℝ := fun _ => speed (-1) 0
  have hb := ADBoundary.bounds ⟨hs.1,hs.2.le⟩
  have hq (t : ℝ) (ht : t∈Icc s (ADBoundary.endpoint s)) : StrictMono (q t) := by
    apply point_strictMono
    exact ⟨by linarith [ht.2.trans_lt hb.2.1],by nlinarith [hb.2.2,ht.1,hs.1],by nlinarith [sq_pos_of_pos hs.1]⟩
  have hqc (i : Fin 4) : ContinuousOn (fun t => q t i) (Icc s (ADBoundary.endpoint s)) := by
    fin_cases i
    · exact continuousOn_const
    · exact continuousOn_const.sub continuousOn_id
    · exact continuousOn_const
    · exact continuousOn_const
  have hqc' (i : Fin 4) : ContinuousOn (fun t => q' t i) (Icc s (ADBoundary.endpoint s)) := continuousOn_const
  have hqd (t : ℝ) (_ : t∈Ioo s (ADBoundary.endpoint s)) (i : Fin 4) : HasDerivAt (fun t => q t i) (q' t i) t := by
    fin_cases i
    · exact hasDerivAt_const _ _
    · change HasDerivAt (fun t : ℝ => 1-t) (-1) t
      simpa only [Pi.sub_apply,id_eq,zero_sub] using! (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)
    · exact hasDerivAt_const _ _
    · exact hasDerivAt_const _ _
  have ht := transport_eq_ratio F j hc hb.1 hp hq hqc hqc' hqd
  have hform : (fun t => j (KZFlat.connection (q t) (q' t)))=
      ADBoundary.movedPole (chords j 4+chords j 3) (chords j 0) (chords j 3) (s^2) := by
    funext t
    rw [show q t=point (1-t) (1-s^2) from rfl,show q' t=speed (-1) 0 from rfl,FourFrames.form_eq,ED_form]
  rw [hform] at ht
  have hqb : q (ADBoundary.endpoint s)=path 3 s := by
    funext i
    fin_cases i <;> simp [q,path,point,FourCollar.cx,FourCollar.cy,ADBoundary.endpoint]
  rw [hqb] at ht
  exact ht

include hc in
theorem ED_insertion {p : Fin 4 → ℝ} (hp : StrictMono p) :
    Ring.inverse (corner F j p 3)*corner F j p 4=
      associator F (chords j 4+chords j 3) (chords j 0) := by
  apply corner_eq_of_limit F j hc hp 4 3
    (ADBoundary.transport_subpower _ _ _ F.cutoff) _ (ED_model_limit F j hc)
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/4)] with s hs
  exact ⟨hs,ED_transport_eq F j hc hp hs⟩

end

open MeasureTheory Set Filter FinitePicard KZCollar PowerAsymptotic PoleEstimate
  KZRectangle StraightKZ
open scoped Topology
attribute [local instance] LieRing.ofAssociativeRing
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
variable (F : NilpotentFiltration A) (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
  (hc : ∀ i,chords j i∈F.space 1)

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem EC_commute_left : Commute (chords j 5+chords j 4+chords j 3) (chords j 5) := by
  rw [add_assoc]
  exact (Commute.refl _).add_left (ED_commute_left j).symm

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem EC_commute_right : Commute (chords j 5+chords j 4+chords j 3) (chords j 3) := by
  rw [add_comm (chords j 5) (chords j 4)]
  exact (BC_commute_right j).symm.add_left (Commute.refl _)

def ECtransport (s : ℝ) : A :=
  transport (ABBoundary.edgeForm (chords j 5) (chords j 3) (chords j 5+chords j 4+chords j 3)
    (chords j 1) (chords j 0) s) s F.cutoff (ABBoundary.endpoint s)

include hc in
theorem EC_model_limit : Tendsto (fun s => inverseModel j 2 s*ECtransport F j s*model j 4 s)
    (𝓝[>] 0) (𝓝 (associator F (chords j 5) (chords j 3))) := by
  have hl := ABBoundary.limit F (chords j 5+chords j 4+chords j 3) (chords j 1) (chords j 0)
    (hc 5) (hc 3) ((F.space 1).add_mem ((F.space 1).add_mem (hc 5) (hc 4)) (hc 3))
    (EC_commute_left j) (EC_commute_right j)
  convert! hl using 1
  funext s
  change KZCollar.gauge (-(chords j 5+chords j 4+2 • chords j 3)) s*ECtransport F j s*
    KZCollar.gauge (2 • chords j 5+chords j 4+chords j 3) s=
    KZCollar.gauge (-(chords j 3+(chords j 5+chords j 4+chords j 3))) s*ECtransport F j s*
    KZCollar.gauge (chords j 5+(chords j 5+chords j 4+chords j 3)) s
  rw [two_smul ℕ,two_smul ℕ,show chords j 5+chords j 4+(chords j 3+chords j 3)=
    chords j 3+(chords j 5+chords j 4+chords j 3) by abel]
  simp only [add_assoc]

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem form_reflection (a b d e f : A) (x y vx vy : ℝ) :
    FourCollar.form a b d e f (1-y) (1-x) (-vy) (-vx)=FourCollar.form f e d b a x y vx vy := by
  unfold FourCollar.form
  rw [show (1-x)-(1-y)=y-x by ring,show -vx- -vy=vy-vx by ring,
    show 1-y-1= -y by ring,show 1-x-1= -x by ring,
    show 1-y= -(y-1) by ring,show 1-x= -(x-1) by ring]
  simp only [neg_div_neg_eq]
  abel

include hc in
theorem EC_transport_eq {p : Fin 4 → ℝ} (hp : StrictMono p) {s : ℝ} (hs : s∈Ioo 0 (1/4)) :
    ECtransport F j s=fundamental F j p (path 2 s)*Ring.inverse (fundamental F j p (path 4 s)) := by
  let q : ℝ → Fin 4 → ℝ := fun t => point (1-ABBoundary.scale s t) (1-t*ABBoundary.scale s t)
  let q' : ℝ → Fin 4 → ℝ := fun t => speed (-ABBoundary.slope s) (-ABBoundary.scaleV s t)
  have hb := ABBoundary.endpoint_bounds ⟨hs.1,hs.2.le⟩
  have hq (t : ℝ) (ht : t∈Icc s (ABBoundary.endpoint s)) : StrictMono (q t) := by
    apply point_strictMono
    have hg := ABBoundary.chamber ⟨hs.1,hs.2.le⟩ ht
    exact ⟨by linarith [hg.2.2],by linarith [hg.2.1],by linarith [hg.1]⟩
  have hqc (i : Fin 4) : ContinuousOn (fun t => q t i) (Icc s (ABBoundary.endpoint s)) := by
    fin_cases i
    · exact continuousOn_const
    · exact (continuous_const.sub (ABBoundary.scale_continuous s)).continuousOn
    · exact (continuous_const.sub (continuous_id.mul (ABBoundary.scale_continuous s))).continuousOn
    · exact continuousOn_const
  have hqc' (i : Fin 4) : ContinuousOn (fun t => q' t i) (Icc s (ABBoundary.endpoint s)) := by
    fin_cases i
    · exact continuousOn_const
    · exact continuousOn_const
    · exact (((ABBoundary.scale_continuous s).add (continuous_id.mul continuous_const)).neg).continuousOn
    · exact continuousOn_const
  have hqd (t : ℝ) (_ : t∈Ioo s (ABBoundary.endpoint s)) (i : Fin 4) : HasDerivAt (fun t => q t i) (q' t i) t := by
    fin_cases i
    · exact hasDerivAt_const _ _
    · change HasDerivAt (fun t => 1-ABBoundary.scale s t) (-ABBoundary.slope s) t
      simpa only [Pi.sub_apply,zero_sub] using! (hasDerivAt_const t (1:ℝ)).sub (ABBoundary.scale_deriv s t)
    · change HasDerivAt (fun t => 1-t*ABBoundary.scale s t) (-ABBoundary.scaleV s t) t
      simpa only [Pi.sub_apply,zero_sub] using! (hasDerivAt_const t (1:ℝ)).sub (ABBoundary.x_deriv s t)
    · exact hasDerivAt_const _ _
  have ht := transport_eq_ratio F j hc hb.2.2 hp hq hqc hqc' hqd
  have hform : Set.EqOn (fun t => j (KZFlat.connection (q t) (q' t)))
      (ABBoundary.edgeForm (chords j 5) (chords j 3) (chords j 5+chords j 4+chords j 3)
        (chords j 1) (chords j 0) s) (Icc s (ABBoundary.endpoint s)) := by
    intro t hti
    dsimp only
    rw [show q t=point (1-ABBoundary.scale s t) (1-t*ABBoundary.scale s t) from rfl,
      show q' t=speed (-ABBoundary.slope s) (-ABBoundary.scaleV s t) from rfl,FourFrames.form_eq,form_reflection,
      ABBoundary.form_eq _ _ _ _ _ ⟨hs.1,hs.2.le⟩ hti]
    simp only [ABBoundary.edgeForm,ABBoundary.error,add_assoc]
  have he := transport_congr (a:=s) (b:=ABBoundary.endpoint s) (by simpa only [uIcc_of_le hb.2.2.le] using hform) F.cutoff
  rw [he] at ht
  have hqb : q (ABBoundary.endpoint s)=path 2 s := by
    funext i
    fin_cases i <;> simp [q,path,point,FourCollar.cx,FourCollar.cy,ABBoundary.scale_end ⟨hs.1,hs.2.le⟩,sub_add_eq_sub_sub]
    have he := ABBoundary.endpoint_mul_scale ⟨hs.1,hs.2.le⟩
    rw [ABBoundary.scale_end ⟨hs.1,hs.2.le⟩] at he
    exact he
  have hqa : q s=path 4 s := by
    funext i
    fin_cases i <;> simp [q,path,point,FourCollar.cx,FourCollar.cy,ABBoundary.scale_start,pow_two]
  rw [hqa,hqb] at ht
  exact ht

include hc in
theorem EC_insertion {p : Fin 4 → ℝ} (hp : StrictMono p) :
    Ring.inverse (corner F j p 2)*corner F j p 4=associator F (chords j 5) (chords j 3) := by
  apply corner_eq_of_limit F j hc hp 4 2
    (ABBoundary.transport_subpower _ _ _ _ _ F.cutoff) _ (EC_model_limit F j hc)
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/4)] with s hs
  exact ⟨hs,EC_transport_eq F j hc hp hs⟩

end FourFrames

end DeligneDrinfeld

end

end OAI
