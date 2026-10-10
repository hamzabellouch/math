import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.EnumeratedRow

namespace OAI

namespace MetricKMedianRecovery.EffectiveOpenability

section
open RationalOpenability
variable {D W F : Type*}

def kindRows (ds : List D) (ws : List W) (fs : List F) : List (Kind D W F) :=
  ds.map .lower ++ ds.map .upper ++
    ds.flatMap (fun j => ws.map (Kind.cap j)) ++ ds.map .far ++ [.payment] ++
    fs.flatMap (fun f => ds.flatMap (fun a => ds.map (Kind.slackZero f a))) ++
    fs.flatMap (fun f => ds.flatMap (fun a => ds.map (Kind.slackTerm f a))) ++
    fs.flatMap (fun f => ds.map (Kind.dual f))

lemma mem_kindRows (ds : List D) (ws : List W) (fs : List F)
    (hd : ∀ j, j∈ds) (hw : ∀ f, f∈ws) (hf : ∀ f, f∈fs) (k : Kind D W F) :
    k ∈ kindRows ds ws fs := by
  cases k <;> simp [kindRows,List.mem_append,List.mem_map,List.mem_flatMap,hd,hw,hf]

lemma length_kindRows (ds : List D) (ws : List W) (fs : List F) :
    (kindRows ds ws fs).length = 3*ds.length+ds.length*ws.length+1+
      2*(fs.length*ds.length*ds.length)+fs.length*ds.length := by
  simp [kindRows,List.length_flatMap,List.map_const',List.sum_replicate]
  ring

def variableEnum (d : ℕ) {m : ℕ} (F : Finset (Fin m)) :
    Fin (d+F.card*(d*d)) ≃ Variables (Fin d) F :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _)
    (finProdFinEquiv.symm.trans (Equiv.prodCongr (F.orderIsoOfFin rfl).toEquiv
      finProdFinEquiv.symm)))

def subtypeList {m : ℕ} (F : Finset (Fin m)) : List F :=
  List.ofFn (F.orderIsoOfFin rfl)

lemma mem_subtypeList {m : ℕ} (F : Finset (Fin m)) (f : F) : f∈subtypeList F := by
  exact List.mem_ofFn.mpr ⟨(F.orderIsoOfFin rfl).symm f,by simp⟩

lemma subtypeList_length {m : ℕ} (F : Finset (Fin m)) : (subtypeList F).length=F.card := by
  simp [subtypeList]

end

open RationalOpenability OpenabilityLinearization

def exactOpening {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : Option (Variables (Fin d) F → ℚ) :=
  solveOpening distance F W v z lam eta i (variableEnum d F)
    (kindRows (List.ofFn (fun j : Fin d => j)) (subtypeList W) (subtypeList F))

lemma exactOpening_sound {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j, (distance f j:ℝ)=dist f (loc j))
    (F W : Finset (Fin m)) (v z lam eta : ℚ) (i : Fin m)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(z:ℝ))
    (x : Variables (Fin d) F → ℚ) (hx : exactOpening distance F W v z lam eta i=some x) :
    etaOpenable loc F W (1-3*(v:ℝ)) (1+(v:ℝ)^2) (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i := by
  apply (openable_iff_linear_feasible loc F W (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i hv hv1 hz).mpr
  refine ⟨fun j => (x (.inl j):ℝ),fun f a j => (x (.inr (f,a,j)):ℝ),?_⟩
  exact solveOpening_sound loc distance hd F W v z lam eta i (variableEnum d F) _
    (mem_kindRows _ _ _ (fun j => List.mem_ofFn.mpr ⟨j,rfl⟩) (mem_subtypeList W)
      (mem_subtypeList F)) x hx

lemma exactOpening_complete {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j, (distance f j:ℝ)=dist f (loc j))
    (F W : Finset (Fin m)) (v z lam eta : ℚ) (i : Fin m)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(z:ℝ))
    (h : etaOpenable loc F W (1-3*(v:ℝ)) (1+(v:ℝ)^2) (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i) :
    ∃ x, exactOpening distance F W v z lam eta i=some x :=
  solveOpening_complete loc distance hd F W v z lam eta i _ _ hv hv1 hz h

lemma exactOpening_none_iff {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j, (distance f j:ℝ)=dist f (loc j))
    (F W : Finset (Fin m)) (v z lam eta : ℚ) (i : Fin m)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(z:ℝ)) :
    exactOpening distance F W v z lam eta i=none ↔
      ¬etaOpenable loc F W (1-3*(v:ℝ)) (1+(v:ℝ)^2) (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i := by
  constructor
  · intro hn ho
    obtain ⟨x,hx⟩ := exactOpening_complete loc distance hd F W v z lam eta i hv hv1 hz ho
    simp [hn] at hx
  · intro hn
    cases he : exactOpening distance F W v z lam eta i with
    | none => rfl
    | some x => exact (hn (exactOpening_sound loc distance hd F W v z lam eta i hv hv1 hz x he)).elim

end MetricKMedianRecovery.EffectiveOpenability

namespace MetricKMedianRecovery.Ellipsoid
open scoped InnerProductSpace

lemma scalar_cut_bound (d s t : ℝ) (hd : 1<d) (hs : s≤1) (ht0 : t≤0) (ht1 : -1≤t) :
    (d^2-1)/d^2*(s+2*t/(d+1)+(1/(d+1))^2)+
      (2*(d+1)/d^2)*(t+1/(d+1))^2 ≤ 1 := by
  have hd0 : d≠0 := by linarith
  have hdp : d+1≠0 := by linarith
  have heq : (d^2-1)/d^2*(s+2*t/(d+1)+(1/(d+1))^2)+
      (2*(d+1)/d^2)*(t+1/(d+1))^2 =
        ((d^2-1)*s+2*(d+1)*(t^2+t)+1)/d^2 := by
    field_simp
    ring
  rw [heq]
  apply (div_le_one (sq_pos_of_ne_zero hd0)).mpr
  have htn : t^2+t≤0 := by
    have hh := mul_nonpos_of_nonpos_of_nonneg ht0 (show 0≤t+1 by linarith)
    nlinarith
  have hh1 := mul_nonneg (show 0≤d^2-1 by nlinarith) (sub_nonneg.mpr hs)
  have hh2 := mul_nonpos_of_nonneg_of_nonpos (show 0≤2*(d+1) by linarith) htn
  nlinarith

lemma unit_ball_cut {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d : ℝ) (hd : 1<d) (u x : E) (hu : ‖u‖=1) (hx : ‖x‖≤1) (hcut : ⟪u,x⟫_ℝ≤0) :
    (d^2-1)/d^2*‖x+(1/(d+1)) • u‖^2+
      (2*(d+1)/d^2)*⟪u,x+(1/(d+1)) • u⟫_ℝ^2 ≤ 1 := by
  have ht1 : -1≤⟪u,x⟫_ℝ := by
    have hh := abs_real_inner_le_norm u x
    rw [hu,one_mul] at hh
    exact (abs_le.mp (hh.trans hx)).1
  have hs : ‖x‖^2≤1 := by nlinarith [norm_nonneg x]
  have hnorm : ‖x+(1/(d+1)) • u‖^2 =
      ‖x‖^2+2*⟪u,x⟫_ℝ/(d+1)+(1/(d+1))^2 := by
    rw [norm_add_sq_real]
    simp only [norm_smul,hu,mul_one,Real.norm_eq_abs,sq_abs,inner_smul_right,
      real_inner_comm x u]
    ring
  have hinner : ⟪u,x+(1/(d+1)) • u⟫_ℝ = ⟪u,x⟫_ℝ+1/(d+1) := by
    simp [inner_add_right,inner_smul_right,hu]
  rw [hnorm,hinner]
  exact scalar_cut_bound d _ _ hd hs hcut ht1

lemma determinant_growth (n : ℕ) (hn : 2≤n) :
    1+1/(n:ℝ) ≤ (( (n:ℝ)^2-1)/(n:ℝ)^2)^n * (((n:ℝ)+1)/((n:ℝ)-1)) := by
  have hp : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hn0 : (n:ℝ)≠0 := by positivity
  have hnm : (n:ℝ)-1≠0 := by linarith
  have hneg : (-1:ℝ)≤ -(1/(n:ℝ)^2) := by
    have hh : (1:ℝ)≤(n:ℝ)^2 := by nlinarith
    have hq : 1/(n:ℝ)^2≤1 := (div_le_one (by positivity)).mpr hh
    linarith
  have hb := one_add_mul_le_pow (show (-2:ℝ)≤ -(1/(n:ℝ)^2) by linarith) n
  have hbase : 1 + -(1/(n:ℝ)^2) = ((n:ℝ)^2-1)/(n:ℝ)^2 := by
    field_simp
    ring
  have hleft : 1+(n:ℝ)*-(1/(n:ℝ)^2) = 1-1/(n:ℝ) := by
    field_simp
    ring
  have hpow : 1-1/(n:ℝ) ≤ (((n:ℝ)^2-1)/(n:ℝ)^2)^n := by
    rwa [hbase,hleft] at hb
  calc
    _ = (1-1/(n:ℝ))*(((n:ℝ)+1)/((n:ℝ)-1)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hpow (div_nonneg (by positivity) (by linarith))

end MetricKMedianRecovery.Ellipsoid

end OAI
