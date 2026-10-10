import OAI.Probability.ContinuumTransition.PressureGeometry

namespace OAI

universe u_1

section
open scoped Topology
open Filter Set
noncomputable section
namespace ContinuumTemperature

def pDot (v w : Parameter) : ℝ := v.1*w.1+v.2*w.2

def SupportOn (S : Set Parameter) (F : Parameter → ℝ) (x v : Parameter) : Prop :=
  ∀ y ∈ S, F x + pDot v (y-x) ≤ F y

def subgradients (S : Set Parameter) (F : Parameter → ℝ) (x : Parameter) : Set Parameter :=
  {v | SupportOn S F x v}

lemma supports_iff_supportOn {F : Parameter → ℝ} {x v : Parameter} :
    Supports F x v ↔ SupportOn pressureDomain F x v := by
  simp only [Supports, SupportOn, pDot, Prod.fst_sub, Prod.snd_sub]
  constructor <;> intro h y hy <;> have := h y hy <;> linarith

lemma linear_parameter_eq (L : Parameter →L[ℝ] ℝ) (x : Parameter) :
    L x = x.1*L (1,0)+x.2*L (0,1) := by
  have he : x = x.1 • ((1,0) : Parameter) + x.2 • ((0,1) : Parameter) := by ext <;> simp
  rw [he,L.map_add,L.map_smul,L.map_smul]
  simp only [smul_eq_mul,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,mul_one,mul_zero,zero_add,add_zero]

lemma linear_epigraph_eq (L : (Parameter × ℝ) →L[ℝ] ℝ) (x : Parameter) (r : ℝ) :
    L (x,r) = x.1*L ((1,0),0)+x.2*L ((0,1),0)+r*L (0,1) := by
  have he : (x,r) = x.1 • (((1,0),0) : Parameter × ℝ) +
      x.2 • (((0,1),0) : Parameter × ℝ) + r • ((0,1) : Parameter × ℝ) := by ext <;> simp
  rw [he,L.map_add,L.map_add,L.map_smul,L.map_smul,L.map_smul]
  simp only [smul_eq_mul]

lemma convex_exists_support {S : Set Parameter} (hS : IsOpen S) {F : Parameter → ℝ}
    (hF : ConvexOn ℝ S F) {x : Parameter} (hx : x ∈ S) :
    ∃ v, SupportOn S F x v := by
  have hcont := hF.continuousOn hS
  have hopen : IsOpen {p : Parameter × ℝ | p.1 ∈ S ∧ F p.1 < p.2} := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have hh : ContinuousAt (fun q : Parameter × ℝ => F q.1) p :=
      (hcont.continuousAt (hS.mem_nhds hp.1)).comp continuousAt_fst
    have hlt := hh.eventually_lt continuousAt_snd hp.2
    filter_upwards [(hS.preimage continuous_fst).mem_nhds hp.1,hlt] with q hq hq'
    exact ⟨hq,hq'⟩
  obtain ⟨L,hL⟩ := geometric_hahn_banach_point_open hF.convex_strict_epigraph hopen
    (x := (x,F x)) (by simp)
  let a := L (0,1)
  let b := L ((1,0),0)
  let c := L ((0,1),0)
  have ha : 0 < a := by
    have hh := hL (x,F x+1) ⟨hx,by linarith⟩
    rw [linear_epigraph_eq L x (F x),linear_epigraph_eq L x (F x+1)] at hh
    dsimp [a]
    nlinarith
  have hle : ∀ y ∈ S, L (x,F x) ≤ L (y,F y) := by
    intro y hy
    apply le_of_forall_pos_le_add
    intro ε hε
    have hh := hL (y,F y+ε/a) ⟨hy,by have := div_pos hε ha; linarith⟩
    rw [linear_epigraph_eq L x (F x),linear_epigraph_eq L y (F y+ε/a)] at hh
    rw [linear_epigraph_eq L x (F x),linear_epigraph_eq L y (F y)]
    change x.1*b+x.2*c+F x*a < y.1*b+y.2*c+(F y+ε/a)*a at hh
    change x.1*b+x.2*c+F x*a ≤ y.1*b+y.2*c+F y*a+ε
    have he : (F y+ε/a)*a = F y*a+ε := by field_simp
    rw [he] at hh
    linarith only [hh]
  refine ⟨(-b/a,-c/a),?_⟩
  intro y hy
  have hh := hle y hy
  rw [linear_epigraph_eq L x (F x),linear_epigraph_eq L y (F y)] at hh
  change F x + ((-b/a)*(y.1-x.1)+(-c/a)*(y.2-x.2)) ≤ F y
  apply (mul_le_mul_iff_left₀ ha).mp
  dsimp [a,b,c] at *
  field_simp
  nlinarith

lemma subgradients_closed (S : Set Parameter) (F : Parameter → ℝ) (x : Parameter) :
    IsClosed (subgradients S F x) := by
  simp only [subgradients,SupportOn,ofPred_forall]
  apply isClosed_iInter
  intro y
  apply isClosed_iInter
  intro _
  exact isClosed_le (by unfold pDot; fun_prop) continuous_const

lemma subgradients_convex (S : Set Parameter) (F : Parameter → ℝ) (x : Parameter) :
    Convex ℝ (subgradients S F x) := by
  intro v hv w hw a b ha hb hab y hy
  have hv' := hv y hy
  have hw' := hw y hy
  have hscaled := add_le_add (mul_le_mul_of_nonneg_left hv' ha) (mul_le_mul_of_nonneg_left hw' hb)
  have hFx := congrArg (fun q : ℝ => q*F x) hab
  have hFy := congrArg (fun q : ℝ => q*F y) hab
  dsimp [pDot] at *
  nlinarith only [hscaled,hFx,hFy]

lemma supportOn_limit {ι : Type u_1} {l : Filter ι} [l.NeBot]
    {S : Set Parameter} {F : Parameter → ℝ} (hF : ContinuousOn F S)
    {x : Parameter} (hx : x ∈ S) {X V : ι → Parameter} {v : Parameter}
    (hX : Tendsto X l (𝓝 x)) (hV : Tendsto V l (𝓝 v))
    (hXS : ∀ᶠ i in l, X i ∈ S) (h : ∀ᶠ i in l, SupportOn S F (X i) (V i)) :
    SupportOn S F x v := by
  intro y hy
  have hf := hF x hx |>.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hX,hXS⟩)
  have hX1 : Tendsto (fun i => (X i).1) l (𝓝 x.1) := (continuous_fst.tendsto x).comp hX
  have hX2 : Tendsto (fun i => (X i).2) l (𝓝 x.2) := (continuous_snd.tendsto x).comp hX
  have hV1 : Tendsto (fun i => (V i).1) l (𝓝 v.1) := (continuous_fst.tendsto v).comp hV
  have hV2 : Tendsto (fun i => (V i).2) l (𝓝 v.2) := (continuous_snd.tendsto v).comp hV
  have hvv : Tendsto (fun i => pDot (V i) (y-X i)) l (𝓝 (pDot v (y-x))) := by
    unfold pDot
    exact (hV1.mul (tendsto_const_nhds.sub hX1)).add
      (hV2.mul (tendsto_const_nhds.sub hX2))
  exact le_of_tendsto (hf.add hvv) (h.mono fun i hi => hi y hy)

end ContinuumTemperature
end
end

end OAI
