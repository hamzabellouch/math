import OAI.MathematicalPhysics.Heisenberg.FlowRouting

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical
open scoped Classical
open Module
open scoped Classical

namespace Heisenberg.Flow

section
open Heisenberg.Geometry Heisenberg.RoutedFlow
variable {k : ℕ}

lemma path_current_decay {Z : Set (ZSite k)} {y a : ZSite k}
    (p : (latticeGraph Zᶜ).Walk y a) (hp : p.IsTrail) {L q : ℝ}
    (hL : 0 ≤ L) (hq : 0 ≤ q) (hnear : ∀ z ∈ p.support, dist z y ≤ L)
    (t : (latticeGraph Zᶜ).Dart) :
    |pathCurrent p t| ≤ (1+L)^q*(1+dist t.fst y)^(-q) := by
  by_cases ht : pathCurrent p t = 0
  · rw [ht,abs_zero]; positivity
  have hz := hnear t.fst (p.dart_fst_mem_support_of_mem_darts ((pathCurrent_ne_zero_iff p t).mp ht))
  have hpos : 0 < 1+dist t.fst y := by positivity
  have hb := Real.rpow_le_rpow (by positivity : 0 ≤ 1+dist t.fst y) (by linarith : 1+dist t.fst y ≤ 1+L) hq
  have hpow : 0 < (1+dist t.fst y)^q := Real.rpow_pos_of_pos hpos _
  have hh : 1 ≤ (1+L)^q*(1+dist t.fst y)^(-q) := by
    rw [Real.rpow_neg hpos.le,mul_comm,← div_eq_inv_mul]
    exact (one_le_div hpow).mpr hb
  exact (pathCurrent_abs_le_one p hp t).trans hh

theorem connected_envelope (hk : 1 ≤ k) (ν C : ℝ) (hν0 : 0 ≤ ν) (hν1 : ν < 1)
    (hq : 0 ≤ (k:ℝ)-(k+1:ℝ)*ν) (hC : 0 ≤ C) :
    ∃ M : ℕ, ∃ B ≥ 0, ∀ (Z : Set (ZSite k)) (_hZ : Z.Finite) (y : ZSite k),
      y ∉ Z → ((ballFinset (k+1) M y).filter (· ∈ Z)).card < 2*(k+1) →
      (∀ z ∈ Z, ∀ w ∈ LatticeComponents.Component Z z, dist z w ≤ C*(1+dist z y)^ν) →
      ∃ J : (latticeGraph Zᶜ).Dart → ℝ,
        (graphNetwork (latticeGraph Zᶜ) (lattice_neighbor_finite Zᶜ)).UnitFlow J y ∧
        ∀ t, |J t| ≤ B*(1+dist t.fst y)^((k+1:ℝ)*ν-k) := by
  obtain ⟨B,hB,D,hD,hflow⟩ := routed_envelope hk ν C hν0 hν1 hC
  let K : ℕ := ⌈D⌉₊
  have hK : 1 ≤ K := by
    have hD' : (1:ℝ) ≤ (K:ℝ) := hD.trans (Nat.le_ceil _)
    exact_mod_cast hD'
  let M := K+2*(k+1)
  let q := (k:ℝ)-(k+1:ℝ)*ν
  let B' := B+(1+(M:ℝ))^q
  have hB' : 0 ≤ B' := add_nonneg hB (Real.rpow_nonneg (by positivity) _)
  refine ⟨M,B',hB',?_⟩
  intro Z hZ y hy hcount hcomp
  obtain ⟨a,ha,hay,J,hunit,hJ⟩ := hflow Z hZ y hcomp
  have haB : a ∈ Ball (K:ℤ) y := (dist_le_iff_mem_ball ..).mp (hay.trans (Nat.le_ceil _))
  obtain ⟨p,hp,_hlen⟩ := local_connectivity (by omega : 2 ≤ k+1) K hK y a Z haB hy ha hcount
  let hom : latticeGraph (Ball (M:ℤ) y \ Z) →g latticeGraph Zᶜ :=
    { toFun := id
      map_rel' := fun h => ⟨h.1,h.2.1.2,h.2.2.2⟩ }
  let P := p.map hom
  have hP : P.IsTrail := (hp.map (by exact Function.injective_id)).isTrail
  have hnear : ∀ z ∈ P.support, dist z y ≤ (M:ℝ) := by
    intro z hz
    have hzp : z ∈ p.support := by
      change z ∈ (p.map hom).support at hz
      rw [SimpleGraph.Walk.support_map,List.mem_map] at hz
      obtain ⟨z',hz',heq⟩ := hz
      change z' = z at heq
      exact heq ▸ hz'
    have hyU : y ∈ Ball ((K:ℤ)+2*(k+1:ℕ)) y \ Z := ⟨by intro j; simp; positivity,hy⟩
    have hzU := path_support_mem _ _ _ hyU p z hzp
    have hzB : z ∈ Ball (M:ℤ) y := by simpa only [M,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hzU.1
    simpa only [dist_comm] using (dist_le_iff_mem_ball y z).mpr hzB
  refine ⟨fun t => J t+pathCurrent P t,?_,?_⟩
  · intro g
    change (graphNetwork (latticeGraph Zᶜ) (lattice_neighbor_finite Zᶜ)).pairing (J + (pathCurrent P : (latticeGraph Zᶜ).Dart → ℝ)) g = g y
    rw [Network.pairing_add,hunit g,pathCurrent_pairing]
    change g a+(g y-g a)=g y
    ring
  · intro t
    have hpbound := path_current_decay P hP (by positivity : 0 ≤ (M:ℝ)) hq hnear t
    have hqeq : -q = (k+1:ℝ)*ν-k := by dsimp [q]; ring
    rw [hqeq] at hpbound
    calc
      _ ≤ |J t|+|pathCurrent P t| := abs_add_le _ _
      _ ≤ B*(1+dist t.fst y)^((k+1:ℝ)*ν-k)+(1+(M:ℝ))^q*(1+dist t.fst y)^((k+1:ℝ)*ν-k) := add_le_add (hJ t) hpbound
      _ = B'*(1+dist t.fst y)^((k+1:ℝ)*ν-k) := by dsimp [B']; ring

end

open Heisenberg.Geometry Heisenberg.LatticeSum
variable {k : ℕ}

def edgeCode {Z : Set (ZSite k)} (e : (latticeGraph Zᶜ).Dart) :
    ↥(ballFinset (k+1) 1 0) × ZSite k :=
  (⟨e.snd-e.fst, by
    apply (mem_ballFinset ..).mpr
    apply (dist_le_iff_mem_ball ..).mp
    simpa only [Nat.cast_one,dist_eq_norm,zero_sub,norm_neg] using step_dist_le_one (step_symm e.adj.1)⟩,e.fst)

lemma edgeCode_injective (Z : Set (ZSite k)) : Function.Injective (edgeCode (Z:=Z)) := by
  intro e f h
  have hfst : e.fst = f.fst := congrArg Prod.snd h
  have hdiff : e.snd-e.fst = f.snd-f.fst := congrArg (fun p : ↥(ballFinset (k+1) 1 0) × ZSite k => (p.1 : ZSite k)) h
  have hsnd : e.snd = f.snd := by rw [hfst] at hdiff; exact sub_left_inj.mp hdiff
  exact SimpleGraph.Dart.ext e f (Prod.ext hfst hsnd)

lemma summable_graph_envelope (Z : Set (ZSite k)) (y : ZSite k) (C r : ℝ)
    (hC : 0 ≤ C) (hr : r < -(k+1:ℝ)) :
    Summable (fun e : (latticeGraph Zᶜ).Dart => C*(1+dist e.fst y)^r) := by
  have hs := summable_radius_sub_rpow (k+1) r (by push_cast; exact hr) y
  have hs' : Summable (fun e : ↥(ballFinset (k+1) 1 0) × ZSite k =>
      C*((radius (e.2-y):ℝ)+1)^r) := by
    apply (summable_prod_of_nonneg (fun e => ?_)).mpr
    · exact ⟨fun _ => hs.mul_left _, .of_finite⟩
    · exact mul_nonneg hC (Real.rpow_nonneg (by positivity) _)
  have hh := hs'.comp_injective (edgeCode_injective Z)
  change Summable (fun e : (latticeGraph Zᶜ).Dart => C*((radius (e.fst-y):ℝ)+1)^r) at hh
  simpa only [radius_eq_norm,dist_eq_norm,add_comm (1:ℝ)] using hh

theorem graph_finite_energy {Z : Set (ZSite k)} (J : (latticeGraph Zᶜ).Dart → ℝ)
    (y : ZSite k) (C q : ℝ) (hC : 0 ≤ C) (hq : (k+1:ℝ) < 2*q)
    (hJ : ∀ e, |J e| ≤ C*(1+dist e.fst y)^(-q)) : Summable (fun e => J e^2) := by
  have he : Summable (fun e : (latticeGraph Zᶜ).Dart => C^2*(1+dist e.fst y)^(-2*q)) :=
    summable_graph_envelope Z y (C^2) (-2*q) (sq_nonneg _) (by linarith)
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ he
  intro e
  have hh := (sq_le_sq₀ (abs_nonneg (J e)) (by positivity : 0 ≤ C*(1+dist e.fst y)^(-q))).mpr (hJ e)
  have hr : ((1+dist e.fst y)^(-q))^2 = (1+dist e.fst y)^(-2*q) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity)]
    congr 1
    ring
  simpa only [sq_abs,mul_pow,hr] using hh

end Heisenberg.Flow

open scoped Classical BigOperators
namespace Heisenberg.FlowOverlap

lemma weighted_half {a b H k q : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hH : 0 < H) (hq : 0 ≤ q) (hHa : H ≤ 2*a) :
    H^q*(a^(-k)*b^(-k)) ≤
      (2:ℝ)^q*(a^(-2*(k-q))+b^(-2*(k-q))) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hpow := Real.rpow_le_rpow hH.le hHa hq
  rw [Real.mul_rpow (by norm_num) ha0.le] at hpow
  have hbq : b^(-k) ≤ b^(-(k-q)) := Real.rpow_le_rpow_of_exponent_le hb (by linarith)
  have hea : a^q*a^(-k) = a^(-(k-q)) := by
    rw [←Real.rpow_add ha0]
    congr 1
    ring
  have hs (x : ℝ) (hx : 0 < x) : (x^(-(k-q)))^2 = x^(-2*(k-q)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hx.le]
    congr 1
    ring
  calc
    _ ≤ ((2:ℝ)^q*a^q)*(a^(-k)*b^(-k)) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = (2:ℝ)^q*(a^(-(k-q))*b^(-k)) := by rw [←hea]; ring
    _ ≤ (2:ℝ)^q*(a^(-(k-q))*b^(-(k-q))) := by gcongr
    _ ≤ (2:ℝ)^q*(a^(-2*(k-q))+b^(-2*(k-q))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [←hs a ha0,←hs b hb0]
      nlinarith [sq_nonneg (a^(-(k-q))-b^(-(k-q))),sq_nonneg (a^(-(k-q))),sq_nonneg (b^(-(k-q)))]

lemma weighted_product {a b H k q : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hH : 0 < H) (hq : 0 ≤ q) (htri : H ≤ a+b) :
    a^(-k)*b^(-k) ≤ (2:ℝ)^q*H^(-q)*
      (a^(-2*(k-q))+b^(-2*(k-q))) := by
  have hw : H^q*(a^(-k)*b^(-k)) ≤
      (2:ℝ)^q*(a^(-2*(k-q))+b^(-2*(k-q))) := by
    by_cases haH : H ≤ 2*a
    · exact weighted_half ha hb hH hq haH
    · have hh := weighted_half (k:=k) hb ha hH hq (show H ≤ 2*b by linarith)
      simpa only [mul_comm (b^(-k)),add_comm (b^(-2*(k-q)))] using hh
  have hh := mul_le_mul_of_nonneg_left hw (Real.rpow_nonneg hH.le (-q))
  have hc : H^(-q)*H^q=1 := by rw [←Real.rpow_add hH]; simp
  calc
    _ = H^(-q)*(H^q*(a^(-k)*b^(-k))) := by rw [←mul_assoc,hc,one_mul]
    _ ≤ _ := by nlinarith [hh]

theorem overlap_sum {E V : Type*} [PseudoMetricSpace V]
    (site : E → V) (J K : E → ℝ) (y z : V) (C k q M : ℝ)
    (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hJ : ∀ e, |J e| ≤ C*(1+dist (site e) y)^(-k))
    (hK : ∀ e, |K e| ≤ C*(1+dist (site e) z)^(-k))
    (hy : Summable (fun e => (1+dist (site e) y)^(-2*(k-q))))
    (hz : Summable (fun e => (1+dist (site e) z)^(-2*(k-q))))
    (hyM : (∑' e, (1+dist (site e) y)^(-2*(k-q))) ≤ M)
    (hzM : (∑' e, (1+dist (site e) z)^(-2*(k-q))) ≤ M) :
    Summable (fun e => |J e*K e|) ∧
    (∑' e, |J e*K e|) ≤ (2*C^2*(2:ℝ)^q*M)*(1+dist y z)^(-q) := by
  let D := C^2*(2:ℝ)^q*(1+dist y z)^(-q)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hs : Summable (fun e => D*((1+dist (site e) y)^(-2*(k-q))+
      (1+dist (site e) z)^(-2*(k-q)))) := (hy.add hz).mul_left D
  have he : ∀ e, |J e*K e| ≤ D*((1+dist (site e) y)^(-2*(k-q))+
      (1+dist (site e) z)^(-2*(k-q))) := by
    intro e
    have ht := dist_triangle y (site e) z
    rw [dist_comm y (site e)] at ht
    have hp := weighted_product (k:=k) (q:=q)
      (show 1 ≤ 1+dist (site e) y by linarith [dist_nonneg (x:=site e) (y:=y)])
      (show 1 ≤ 1+dist (site e) z by linarith [dist_nonneg (x:=site e) (y:=z)])
      (show 0 < 1+dist y z by positivity) hq (by linarith)
    calc
      _ = |J e| * |K e| := abs_mul ..
      _ ≤ (C*(1+dist (site e) y)^(-k))*(C*(1+dist (site e) z)^(-k)) :=
        mul_le_mul (hJ e) (hK e) (abs_nonneg _) (by positivity)
      _ = C^2*((1+dist (site e) y)^(-k)*(1+dist (site e) z)^(-k)) := by ring
      _ ≤ C^2*((2:ℝ)^q*(1+dist y z)^(-q)*
          ((1+dist (site e) y)^(-2*(k-q))+(1+dist (site e) z)^(-2*(k-q)))) :=
        mul_le_mul_of_nonneg_left hp (sq_nonneg C)
      _ = _ := by dsimp [D]; ring
  have hsum := Summable.of_nonneg_of_le (fun _ => abs_nonneg _) he hs
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑' e, D*((1+dist (site e) y)^(-2*(k-q))+(1+dist (site e) z)^(-2*(k-q))) :=
      hsum.tsum_le_tsum he hs
    _ = D*((∑' e, (1+dist (site e) y)^(-2*(k-q)))+
        (∑' e, (1+dist (site e) z)^(-2*(k-q)))) := by rw [tsum_mul_left,hy.tsum_add hz]
    _ ≤ D*(M+M) := mul_le_mul_of_nonneg_left (add_le_add hyM hzM) hD
    _ = _ := by dsimp [D]; ring

end Heisenberg.FlowOverlap

namespace Heisenberg.Flow
open Heisenberg.Geometry Heisenberg.LatticeSum
variable {k : ℕ}

lemma uniform_graph_sum (r : ℝ) (hr : r < -(k+1:ℝ)) :
    ∃ M ≥ 0, ∀ (Z : Set (ZSite k)) (y : ZSite k),
      Summable (fun e : (latticeGraph Zᶜ).Dart => (1+dist e.fst y)^r) ∧
      (∑' e : (latticeGraph Zᶜ).Dart, (1+dist e.fst y)^r) ≤ M := by
  let S := ∑' x : ZSite k, ((radius x:ℝ)+1)^r
  let M := (Fintype.card ↥(ballFinset (k+1) 1 0):ℝ)*S
  have hS : 0 ≤ S := tsum_nonneg (fun x => Real.rpow_nonneg (by positivity) _)
  refine ⟨M,mul_nonneg (Nat.cast_nonneg _) hS,?_⟩
  intro Z y
  have hs := summable_radius_sub_rpow (k+1) r (by push_cast; exact hr) y
  have htrans : (∑' x : ZSite k, ((radius (x-y):ℝ)+1)^r) = S :=
    (Equiv.subRight y).tsum_eq (fun x : ZSite k => ((radius x:ℝ)+1)^r)
  let F : ↥(ballFinset (k+1) 1 0) × ZSite k → ℝ :=
    fun e => ((radius (e.2-y):ℝ)+1)^r
  have hsF : Summable F := by
    apply (summable_prod_of_nonneg (fun _ => Real.rpow_nonneg (by positivity) _)).mpr
    exact ⟨fun _ => hs, .of_finite⟩
  have hcomp := hsF.comp_injective (edgeCode_injective Z)
  have hbound := tsum_comp_le_tsum_of_inj hsF
    (fun e => Real.rpow_nonneg (by positivity : 0 ≤ (radius (e.2-y):ℝ)+1) r) (edgeCode_injective Z)
  have htotal : (∑' e, F e) = M := by
    rw [hsF.tsum_prod,tsum_fintype]
    simp only [F,htrans,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rfl
  refine ⟨?_,?_⟩
  · simpa only [Function.comp_def,F,edgeCode,radius_eq_norm,dist_eq_norm,add_comm (1:ℝ)] using hcomp
  · rw [htotal] at hbound
    simpa only [Function.comp_def,F,edgeCode,radius_eq_norm,dist_eq_norm,add_comm (1:ℝ)] using hbound

theorem graph_overlap_uniform (κ q C : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hexp : (k+1:ℝ) < 2*(κ-q)) :
    ∃ B ≥ 0, ∀ (Z : Set (ZSite k)) (y z : ZSite k)
      (J K : (latticeGraph Zᶜ).Dart → ℝ),
      (∀ e, |J e| ≤ C*(1+dist e.fst y)^(-κ)) →
      (∀ e, |K e| ≤ C*(1+dist e.fst z)^(-κ)) →
      Summable (fun e => |J e*K e|) ∧
      (∑' e, |J e*K e|) ≤ B*(1+dist y z)^(-q) := by
  obtain ⟨M,hM,huniform⟩ := uniform_graph_sum (k:=k) (-2*(κ-q)) (by linarith)
  refine ⟨2*C^2*(2:ℝ)^q*M,by positivity,?_⟩
  intro Z y z J K hJ hK
  exact Heisenberg.FlowOverlap.overlap_sum (fun e : (latticeGraph Zᶜ).Dart => e.fst) J K y z C κ q M hC hq
    hJ hK (huniform Z y).1 (huniform Z z).1 (huniform Z y).2 (huniform Z z).2

end Heisenberg.Flow

end

end OAI
