import OAI.Dynamics.ThreeTorus.PassageFamilies
import OAI.Dynamics.ThreeTorus.PacketStates

namespace OAI

/-! Finite passage geometry families, physical charts, and all-jet bounds. -/

section

/-! Bookkeeping for an ACTUAL geometric passage family. All fields are produced
by the unconditional neutral/signal theorems, not assumed as a main theorem
interface. This keeps the geometric data attached during finite iteration. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

structure PassageGeometryFamily (V : ℝ → ℝ) where
  c : ℕ
  c_pos : 0 < c
  Δ : ℕ → ℝ
  H : ℕ → UnitAddCircle → UnitAddCircle
  J : UnitAddCircle → ℝ
  J₀ : ℝ → ℝ
  Jmatch : ∀ x : ℝ, J (x:UnitAddCircle) = J₀ x
  Jcontinuous : Continuous J
  delta_bound : ∀ n, 0 < n → |Δ n| ≤ (n:ℝ)⁻¹
  delta_tendsto : Tendsto Δ atTop (𝓝 0)
  Hcontinuous : ∀ n, Continuous (H n)
  Hformula : ∀ n (x : ℝ), H n (x:UnitAddCircle) =
    ((n:ℝ)*((∫ t in 0..x, (c:ℝ)+V t)+Δ n*x):UnitAddCircle)
  geometry : ∀ n : ℕ, let σ := fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)
    Smooth (torusPassage (H n) σ) ∧ Smooth (torusPassage (H n) σ).symm ∧
      MeasurePreserving (torusPassage (H n) σ) μ μ
  graph : ∀ n, 0 < n → ∀ x : Cover,
    torusPassage (H n) (fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)) (project x) =
      project (passageFamily (fun t => (c:ℝ)+V t) J₀ 1 ((n:ℝ)⁻¹,Δ n) x) ∧
    (torusPassage (H n) (fun a => (((1+J a/n)/n:ℝ):UnitAddCircle))).symm (project x) =
      project (passageFamily (fun t => (c:ℝ)+V t) J₀ (-1) ((n:ℝ)⁻¹,Δ n) x)
  convergence : ∀ r : ℝ, ∀ K : Set Cover, IsCompact K → ∀ d : ℕ,
    TendstoUniformlyOn
      (fun (n : ℕ) x => iteratedFDeriv ℝ d
        (passageFamily (fun t => (c:ℝ)+V t) J₀ r ((n:ℝ)⁻¹,Δ n)) x)
      (fun x => iteratedFDeriv ℝ d (fun y : Cover => ![y 0+r*((c:ℝ)+V (y 1)),y 1,y 2]) x)
      atTop K

namespace PassageGeometryFamily
variable {V : ℝ → ℝ} (g : PassageGeometryFamily V)
def sigma (n : ℕ) (a : UnitAddCircle) : UnitAddCircle := (((1+g.J a/n)/n:ℝ):UnitAddCircle)
def scale (B : ℝ) (n : ℕ) : ℝ := (n:ℝ)*g.c*B
lemma scale_pos {B : ℝ} (hB : 0 < B) {n : ℕ} (hn : 0 < n) : 0 < g.scale B n := by
  unfold scale
  exact mul_pos (mul_pos (by exact_mod_cast hn) (by exact_mod_cast g.c_pos)) hB
lemma sigma_continuous (n : ℕ) : Continuous (g.sigma n) :=
  (AddCircle.continuous_mk' 1).comp ((continuous_const.add (g.Jcontinuous.div_const _)).div_const _)
end PassageGeometryFamily

/-- The linked support displacement of an actual next state. The old support
point is shared by the index and every temporal comparison. -/
def StateTracks {ι κ : Type*} (F : PassagePackets ι) (G : PassagePackets κ)
    (parent : κ → ι) (B B' η : ℝ) : Prop :=
  ∀ i, ∃ x ∈ F.core (parent i),
    |(G.m i:ℝ)/B'-(F.m (parent i):ℝ)/B| < η ∧
    ∀ y, dist ((G.m i:ℝ)*G.V y:UnitAddCircle)
      ((F.m (parent i):ℝ)*F.V x:UnitAddCircle) < η

lemma StateTracks.density {ι κ : Type*} {F : PassagePackets ι} {G : PassagePackets κ}
    {parent : κ → ι} {B B' η : ℝ} (h : StateTracks F G parent B B' η) :
    ∀ j z, G.density j z ≠ 0 → ∃ x ∈ F.core (parent j),
      |(G.m j:ℝ)/B'-(F.m (parent j):ℝ)/B| < η ∧
      dist z ((F.m (parent j):ℝ)*F.V x:UnitAddCircle) < η := by
  intro j z hz
  obtain ⟨x,hx,ha,ht⟩ := h j
  obtain ⟨y,_hy,he⟩ := G.density_support j hz
  exact ⟨x,hx,ha,he ▸ ht y⟩

lemma StateTracks.mono {ι κ : Type*} {F : PassagePackets ι} {G : PassagePackets κ}
    {parent : κ → ι} {B B' η η' : ℝ} (h : StateTracks F G parent B B' η) (hh : η ≤ η') :
    StateTracks F G parent B B' η' := by
  intro i
  obtain ⟨x,hx,ha,ht⟩ := h i
  exact ⟨x,hx,ha.trans_le hh,fun y => (ht y).trans_le hh⟩

lemma StateTracks.trans {ι κ ν : Type*} {F : PassagePackets ι} {G : PassagePackets κ}
    {K : PassagePackets ν} {p : κ → ι} {q : ν → κ} {B B' B'' η η' : ℝ}
    (h : StateTracks F G p B B' η) (h' : StateTracks G K q B' B'' η') :
    StateTracks F K (p ∘ q) B B'' (η+η') := by
  intro i
  obtain ⟨x,hx,ha,ht⟩ := h (q i)
  obtain ⟨y,_hy,hb,hs⟩ := h' i
  refine ⟨x,hx,?_,?_⟩
  · have hh := (abs_sub_le ((K.m i:ℝ)/B'') ((G.m (q i):ℝ)/B') ((F.m (p (q i)):ℝ)/B))
    calc
      _ ≤ |(K.m i:ℝ)/B''-(G.m (q i):ℝ)/B'|+|(G.m (q i):ℝ)/B'-(F.m (p (q i)):ℝ)/B| := hh
      _ < η'+η := add_lt_add hb ha
      _ = η+η' := add_comm _ _
  · intro z
    calc
      _ ≤ dist ((K.m i:ℝ)*K.V z:UnitAddCircle) ((G.m (q i):ℝ)*G.V y:UnitAddCircle)+
        dist ((G.m (q i):ℝ)*G.V y:UnitAddCircle) ((F.m (p (q i)):ℝ)*F.V x:UnitAddCircle) := dist_triangle _ _ _
      _ < η'+η := add_lt_add (hs z) (ht y)
      _ = η+η' := add_comm _ _

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace PassageGeometryFamily
variable {V : ℝ → ℝ} (g : PassageGeometryFamily V)

/-- Smoothness of the retained speed recovers smoothness of the actual jitter;
no additional regularity hypothesis on a passage is needed. -/
lemma smooth_jitter_of_output {ι : Type*} (G : PassagePackets ι) {n : ℕ}
    (hn : 0 < n) (hG : G.V = fun x => (1+g.J₀ x/n)/n) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g.J₀ := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have he : g.J₀ = fun x => (n:ℝ)*((n:ℝ)*G.V x-1) := by
    funext x
    rw [hG]
    field_simp
    ring
  rw [he]
  exact contDiff_const.mul ((contDiff_const.mul G.smooth_speed).sub contDiff_const)

/-- The integer carrier contributes only a deck translation. Removing it
makes the limit the literal old twist lift, including at derivative order 0. -/
def correctedFamily (r : ℝ) (p : ℝ × ℝ) (x : Cover) : Cover :=
  passageFamily (fun t => (g.c:ℝ)+V t) g.J₀ r p x - ![r*(g.c:ℝ),0,0]

lemma correctedFamily_zero (r : ℝ) : g.correctedFamily r (0,0) =
    fun x : Cover => ![x 0+r*V (x 1),x 1,x 2] := by
  funext x
  rw [correctedFamily,passageFamily_zero]
  ext i
  fin_cases i <;> simp
  ring

lemma correctedFamily_smooth (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g.J₀) (r : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (ℝ × ℝ) × Cover => g.correctedFamily r p.1 p.2) :=
  (smooth_passageFamily (contDiff_const.add hV) hJ r).sub contDiff_const

/-- Every spatial jet still converges after an arbitrary fixed smooth change
of physical coordinates. Both signs of the map use this same theorem. -/
lemma physical_jets_tendsto (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g.J₀)
    {A B : Cover → Cover} (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    (r : ℝ) {K : Set Cover} (hK : IsCompact K) (d : ℕ) :
    TendstoUniformlyOn
      (fun (n : ℕ) x => iteratedFDeriv ℝ d
        (fun y => B (g.correctedFamily r ((n:ℝ)⁻¹,g.Δ n) (A y))) x)
      (fun x => iteratedFDeriv ℝ d
        (fun y => B ![A y 0+r*V (A y 1),A y 1,A y 2]) x) atTop K := by
  have hs := hB.comp ((g.correctedFamily_smooth hV hJ r).comp
    (contDiff_fst.prodMk (hA.comp contDiff_snd)))
  have ht := smooth_parameter_jets_tendsto hs (0,0) hK d
  have he (x : Cover) : g.correctedFamily r (0,0) (A x) =
      ![A x 0+r*V (A x 1),A x 1,A x 2] := congrFun (g.correctedFamily_zero r) (A x)
  change TendstoUniformlyOn
    (fun a x => iteratedFDeriv ℝ d (fun y => B (g.correctedFamily r a (A y))) x)
    (fun x => iteratedFDeriv ℝ d (fun y => B (g.correctedFamily r (0,0) (A y))) x)
    (𝓝 (0,0)) K at ht
  simp only [he] at ht
  exact fun U hU => (passage_parameters_tendsto g.delta_bound).eventually (ht U hU)

/-- Any finite list of physical smooth seminorm restrictions can be imposed
before selecting the passage integer, simultaneously for map and inverse. -/
lemma eventually_physical_jets {ι : Type*} [Fintype ι]
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g.J₀)
    {A B : Cover → Cover} (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    (r : ι → ℝ) (K : ι → Set Cover) (hK : ∀ i, IsCompact (K i)) (d : ι → ℕ)
    (ε : ι → ℝ) (he : ∀ i, 0 < ε i) :
    ∀ᶠ n : ℕ in atTop, ∀ i x, x ∈ K i →
      dist (iteratedFDeriv ℝ (d i)
        (fun y => B (g.correctedFamily (r i) ((n:ℝ)⁻¹,g.Δ n) (A y))) x)
        (iteratedFDeriv ℝ (d i)
          (fun y => B ![A y 0+r i*V (A y 1),A y 1,A y 2]) x) < ε i := by
  apply eventually_all.2
  intro i
  simpa only [dist_comm] using (Metric.tendstoUniformlyOn_iff.1 (g.physical_jets_tendsto hV hJ hA hB
    (r i) (hK i) (d i))) (ε i) (he i)

end PassageGeometryFamily
end ThreeTorus
end
end

section

/-! Global smooth cover charts with independently chosen deck representatives
for the two signs. This makes the corrected physical passage lift compatible
with further coordinate changes, rather than losing the integer carrier. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

def tripleProject (x : Cover) : TripleTorus := torusTriple (project x)

def coverTwist (V : ℝ → ℝ) (r : ℝ) (x : Cover) : Cover :=
  ![x 0+r*V (x 1),x 1,x 2]

def coverChart (h : ℝ → ℝ) (x : Cover) : Cover := ![x 1,x 2,x 0-h (x 1)]
def coverChartInv (h : ℝ → ℝ) (x : Cover) : Cover := ![x 2+h (x 0),x 0,x 1]

def coverDeck (k : ℤ) (x : Cover) : Cover := ![x 0+(k:ℝ),x 1,x 2]

lemma smooth_coverChart {h : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (coverChart h) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [coverChart] <;> fun_prop

lemma smooth_coverChartInv {h : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (coverChartInv h) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [coverChartInv] <;> fun_prop

lemma smooth_coverDeck (k : ℤ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (coverDeck k) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [coverDeck] <;> fun_prop

lemma tripleProject_coverDeck (k : ℤ) (x : Cover) : tripleProject (coverDeck k x) = tripleProject x := by
  change (((x 0+(k:ℝ):ℝ):UnitAddCircle),(x 1:UnitAddCircle),(x 2:UnitAddCircle)) = _
  rw [AddCircle.coe_add]
  have hz : ((k:ℝ):UnitAddCircle) = 0 := by
    rw [← mul_one (k:ℝ),← zsmul_eq_mul,AddCircle.coe_zsmul,AddCircle.coe_period,smul_zero]
  rw [hz,add_zero]
  rfl

lemma coverChart_graph {h : ℝ → ℝ} {H : UnitAddCircle → UnitAddCircle}
    (hH : ∀ x : ℝ, H (x:UnitAddCircle) = (h x:UnitAddCircle)) (x : Cover) :
    tripleProject (coverChart h x) = passageChart H (tripleProject x) := by
  change ((x 1:UnitAddCircle),(x 2:UnitAddCircle),((x 0-h (x 1):ℝ):UnitAddCircle)) =
    ((x 1:UnitAddCircle),(x 2:UnitAddCircle),(x 0:UnitAddCircle)+(-H (x 1:UnitAddCircle)))
  rw [AddCircle.coe_sub,hH,sub_eq_add_neg]

lemma coverChartInv_graph {h : ℝ → ℝ} {H : UnitAddCircle → UnitAddCircle}
    (hH : ∀ x : ℝ, H (x:UnitAddCircle) = (h x:UnitAddCircle)) (x : Cover) :
    tripleProject (coverChartInv h x) = (passageChart H).symm (tripleProject x) := by
  change (((x 2+h (x 0):ℝ):UnitAddCircle),(x 0:UnitAddCircle),(x 1:UnitAddCircle)) =
    ((x 2:UnitAddCircle)-(-H (x 0:UnitAddCircle)),(x 0:UnitAddCircle),(x 1:UnitAddCircle))
  rw [AddCircle.coe_add,hH,sub_neg_eq_add]

structure PhysicalFrame where
  chart : Equiv.Perm TripleTorus
  forward : Cover → Cover
  backward : ℤ → Cover → Cover
  forward_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) forward
  backward_smooth : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (backward k)
  forward_graph : ∀ x, tripleProject (forward x) = chart (tripleProject x)
  backward_graph : ∀ k x, tripleProject (backward k x) = chart.symm (tripleProject x)

namespace PhysicalFrame

def ident : PhysicalFrame where
  chart := Equiv.refl _
  forward := id
  backward := fun _ => id
  forward_smooth := contDiff_id
  backward_smooth := fun _ => contDiff_id
  forward_graph := fun _ => rfl
  backward_graph := fun _ _ => rfl

def mapLift (F : PhysicalFrame) (V : ℝ → ℝ) (k : ℤ) : Cover → Cover :=
  F.backward k ∘ coverTwist V (k:ℝ) ∘ F.forward

lemma mapLift_smooth (F : PhysicalFrame) {V : ℝ → ℝ}
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (k : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F.mapLift V k) := by
  apply (F.backward_smooth k).comp
  apply ContDiff.comp _ F.forward_smooth
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [coverTwist] <;> fun_prop

end PhysicalFrame

namespace PassageGeometryFamily
variable {V : ℝ → ℝ} (g : PassageGeometryFamily V)

def primitive (n : ℕ) (x : ℝ) : ℝ := ∫ t in 0..x, (n:ℝ)*((g.c:ℝ)+V t+g.Δ n)

lemma primitive_smooth (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g.primitive n) :=
  contDiff_real_primitive (contDiff_const.mul ((contDiff_const.add hV).add contDiff_const))

lemma primitive_matches (hV : Continuous V) (n : ℕ) (x : ℝ) :
    g.H n (x:UnitAddCircle) = (g.primitive n x:UnitAddCircle) := by
  rw [g.Hformula,primitive,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (f := fun t => (g.c:ℝ)+V t) (g := fun _ => g.Δ n) ((continuous_const.add hV : Continuous (fun t => (g.c:ℝ)+V t)).intervalIntegrable 0 x)
      (continuous_const.intervalIntegrable 0 x)]
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_comm (g.Δ n) x]

lemma chart_twist_chartInv (hV : Continuous V) {n : ℕ} (hn : 0 < n) (r : ℝ) (x : Cover) :
    coverChartInv (g.primitive n) (coverTwist (fun a => (1+g.J₀ a/n)/n) r
      (coverChart (g.primitive n) x)) =
      passageFamily (fun t => (g.c:ℝ)+V t) g.J₀ r ((n:ℝ)⁻¹,g.Δ n) x := by
  have hi := passageFamily_increment (v := fun t => (g.c:ℝ)+V t) (J := g.J₀) (continuous_const.add hV) hn (g.Δ n) r (x 1) (x 2)
  have he (a : ℝ) : (1+g.J₀ a/n)/n = (n:ℝ)⁻¹+(n:ℝ)⁻¹^2*g.J₀ a := by
    simp only [div_eq_mul_inv]
    ring
  have hs : r*((n:ℝ)⁻¹+(n:ℝ)⁻¹^2*g.J₀ (x 2)) =
      r*(n:ℝ)⁻¹*(1+(n:ℝ)⁻¹*g.J₀ (x 2)) := by ring
  ext i
  fin_cases i
  · dsimp [coverChartInv,coverChart,coverTwist,passageFamily,primitive]
    rw [he]
    linarith [hi]
  · dsimp [coverChartInv,coverChart,coverTwist,passageFamily]
    rw [he,hs]
  · rfl

end PassageGeometryFamily

namespace PhysicalFrame

def next (F : PhysicalFrame) {V : ℝ → ℝ} (g : PassageGeometryFamily V)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (n : ℕ) : PhysicalFrame where
  chart := F.chart.trans (passageChart (g.H n))
  forward := coverChart (g.primitive n) ∘ F.forward
  backward := fun k => F.backward k ∘ coverDeck (-k*(g.c:ℤ)) ∘ coverChartInv (g.primitive n)
  forward_smooth := (smooth_coverChart (g.primitive_smooth hV n)).comp F.forward_smooth
  backward_smooth := fun k => (F.backward_smooth k).comp ((smooth_coverDeck _).comp
    (smooth_coverChartInv (g.primitive_smooth hV n)))
  forward_graph := by
    intro x
    dsimp only [Function.comp_apply,Equiv.trans_apply]
    rw [coverChart_graph (g.primitive_matches hV.continuous n),F.forward_graph]
  backward_graph := by
    intro k x
    dsimp only [Function.comp_apply,Equiv.symm_trans_apply]
    rw [F.backward_graph,tripleProject_coverDeck,coverChartInv_graph (g.primitive_matches hV.continuous n)]

lemma next_mapLift (F : PhysicalFrame) {V : ℝ → ℝ} (g : PassageGeometryFamily V)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) {n : ℕ} (hn : 0 < n) (k : ℤ) :
    (F.next g hV n).mapLift (fun a => (1+g.J₀ a/n)/n) k =
      fun x => F.backward k (g.correctedFamily (k:ℝ) ((n:ℝ)⁻¹,g.Δ n) (F.forward x)) := by
  funext x
  change F.backward k (coverDeck (-k*(g.c:ℤ))
    (coverChartInv (g.primitive n) (coverTwist _ (k:ℝ) (coverChart (g.primitive n) (F.forward x))))) = _
  rw [g.chart_twist_chartInv hV.continuous hn]
  congr 1
  ext i
  fin_cases i <;> simp [coverDeck,PassageGeometryFamily.correctedFamily,sub_eq_add_neg]

end PhysicalFrame
end ThreeTorus
end
end

section

/-! Finite summation and composition estimates in the original physical L².
These let the literal per-packet passages be assembled without replacing their
vectors by independent spectral models. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

def physicalError (f g : TripleTorus → ℂ) : ℝ :=
  ∫ x, ‖f x-g x‖^2 ∂tripleVolume

lemma physicalError_integrable {f g : TripleTorus → ℂ} (hf : Continuous f) (hg : Continuous g) :
    Integrable (fun x => ‖f x-g x‖^2) tripleVolume :=
  ((hf.sub hg).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma physicalError_nonneg (f g : TripleTorus → ℂ) : 0 ≤ physicalError f g :=
  integral_nonneg (fun _ => sq_nonneg _)

lemma physicalError_chart {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H)
    (f g : TripleTorus → ℂ) :
    physicalError (f ∘ passageChart H) (g ∘ passageChart H) = physicalError f g :=
  integral_passageChart hH (fun x => ‖f x-g x‖^2)

lemma physicalError_triangle {f g h : TripleTorus → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    physicalError f h ≤ 2*physicalError f g+2*physicalError g h := by
  have hp x : ‖f x-h x‖^2 ≤ 2*‖f x-g x‖^2+2*‖g x-h x‖^2 := by
    have hn : ‖f x-h x‖^2 ≤ (‖f x-g x‖+‖g x-h x‖)^2 := by
      gcongr
      simpa only [dist_eq_norm] using dist_triangle (f x) (g x) (h x)
    nlinarith [sq_nonneg (‖f x-g x‖-‖g x-h x‖)]
  unfold physicalError
  calc
    _ ≤ ∫ x, 2*‖f x-g x‖^2+2*‖g x-h x‖^2 ∂tripleVolume :=
      integral_mono (physicalError_integrable hf hh)
        (((physicalError_integrable hf hg).const_mul 2).add ((physicalError_integrable hg hh).const_mul 2)) hp
    _ = _ := by
      rw [integral_add ((physicalError_integrable hf hg).const_mul 2)
        ((physicalError_integrable hg hh).const_mul 2),integral_const_mul,integral_const_mul]

lemma physicalError_sum {ι : Type*} [Fintype ι] {f g : ι → TripleTorus → ℂ}
    (hf : ∀ i, Continuous (f i)) (hg : ∀ i, Continuous (g i)) :
    physicalError (fun x => ∑ i, f i x) (fun x => ∑ i, g i x) ≤
      (Fintype.card ι:ℝ)*(∑ i, physicalError (f i) (g i)) := by
  have he x : (∑ i, f i x)-(∑ i, g i x) = ∑ i, (f i x-g i x) :=
    (Finset.sum_sub_distrib _ _).symm
  have hp x : ‖(∑ i, f i x)-(∑ i, g i x)‖^2 ≤
      (Fintype.card ι:ℝ)*(∑ i, ‖f i x-g i x‖^2) := by
    rw [he]
    calc
      _ ≤ (∑ i, ‖f i x-g i x‖)^2 := by
        gcongr
        exact norm_sum_le _ _
      _ ≤ _ := by simpa only [Finset.card_univ] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖f i x-g i x‖))
  unfold physicalError
  calc
    _ ≤ ∫ x, (Fintype.card ι:ℝ)*(∑ i, ‖f i x-g i x‖^2) ∂tripleVolume :=
      integral_mono
        (physicalError_integrable (continuous_finsetSum _ (fun i _ => hf i))
          (continuous_finsetSum _ (fun i _ => hg i)))
        ((integrable_finsetSum _ (fun i _ => physicalError_integrable (hf i) (hg i))).const_mul _) hp
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum _ (fun i _ => physicalError_integrable (hf i) (hg i))]

end ThreeTorus
end
end

end OAI
