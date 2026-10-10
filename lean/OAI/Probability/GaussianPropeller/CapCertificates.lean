import OAI.Probability.GaussianPropeller.LossCertificates

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.FourCertificates
noncomputable def affine (r:ℝ) := (108/125:ℝ)*r^2+(143/5000:ℝ)

lemma cap_envelope {r P F:ℝ} (_hP:P≤1/2) (hF:F≤1/2)
    (hcap:r≤(8/3:ℝ)*P*(1-P)) (hpoly:(8/3:ℝ)*F*(1-F)≤r) : F≤P := by
  by_contra hn
  have hd : 0<F-P := sub_pos.mpr (lt_of_not_ge hn)
  have he : 0<(F-P)*(1-P-F) := mul_pos hd (by linarith only [hd,hF])
  nlinarith only [he,hcap,hpoly]

lemma affine_cap_poly_0 {r:ℝ} (hr:r∈Icc (39/250:ℝ) (617/1500:ℝ)) :
    (8/3:ℝ)*affine r*(1-affine r)≤r := by
  have hl : 0≤r-(39/250:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(617/1500:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) =
    (2391277896991494/336213480015625:ℝ)*(r-(39/250:ℝ))^0*((617/1500:ℝ)-r)^4 + (16684638404902488/336213480015625:ℝ)*(r-(39/250:ℝ))^1*((617/1500:ℝ)-r)^3 + (26003061476182116/336213480015625:ℝ)*(r-(39/250:ℝ))^2*((617/1500:ℝ)-r)^2 + (13152961928422872/336213480015625:ℝ)*(r-(39/250:ℝ))^3*((617/1500:ℝ)-r)^1 + (2112546341425734/336213480015625:ℝ)*(r-(39/250:ℝ))^4*((617/1500:ℝ)-r)^0 := by unfold affine; ring
  have hp : 0≤r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma affine_cap_poly_1 {r:ℝ} (hr:r∈Icc (617/1500:ℝ) (539/1000:ℝ)) :
    (8/3:ℝ)*affine r*(1-affine r)≤r := by
  have hl : 0≤r-(617/1500:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(539/1000:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) =
    (33800741462811744/336213480015625:ℝ)*(r-(617/1500:ℝ))^0*((539/1000:ℝ)-r)^4 + (97580753349487488/336213480015625:ℝ)*(r-(617/1500:ℝ))^1*((539/1000:ℝ)-r)^3 + (86815626229463616/336213480015625:ℝ)*(r-(617/1500:ℝ))^2*((539/1000:ℝ)-r)^2 + (24717526517503872/336213480015625:ℝ)*(r-(617/1500:ℝ))^3*((539/1000:ℝ)-r)^1 + (2351197555989984/336213480015625:ℝ)*(r-(617/1500:ℝ))^4*((539/1000:ℝ)-r)^0 := by unfold affine; ring
  have hp : 0≤r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma affine_cap_poly_2 {r:ℝ} (hr:r∈Icc (539/1000:ℝ) (6851/12000:ℝ)) :
    (8/3:ℝ)*affine r*(1-affine r)≤r := by
  have hl : 0≤r-(539/1000:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(6851/12000:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) =
    (601906574333435904/336213480015625:ℝ)*(r-(539/1000:ℝ))^0*((6851/12000:ℝ)-r)^4 + (1427611174546931712/336213480015625:ℝ)*(r-(539/1000:ℝ))^1*((6851/12000:ℝ)-r)^3 + (1099717789846450176/336213480015625:ℝ)*(r-(539/1000:ℝ))^2*((6851/12000:ℝ)-r)^2 + (369439192509401088/336213480015625:ℝ)*(r-(539/1000:ℝ))^3*((6851/12000:ℝ)-r)^1 + (96095288257720704/336213480015625:ℝ)*(r-(539/1000:ℝ))^4*((6851/12000:ℝ)-r)^0 := by unfold affine; ring
  have hp : 0≤r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma affine_cap_poly_3 {r:ℝ} (hr:r∈Icc (6851/12000:ℝ) (3617/6000:ℝ)) :
    (8/3:ℝ)*affine r*(1-affine r)≤r := by
  have hl : 0≤r-(6851/12000:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(3617/6000:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) =
    (96095288257720704/336213480015625:ℝ)*(r-(6851/12000:ℝ))^0*((3617/6000:ℝ)-r)^4 + (399323113552364544/336213480015625:ℝ)*(r-(6851/12000:ℝ))^1*((3617/6000:ℝ)-r)^3 + (1189369552975340544/336213480015625:ℝ)*(r-(6851/12000:ℝ))^2*((3617/6000:ℝ)-r)^2 + (1613038898973118464/336213480015625:ℝ)*(r-(6851/12000:ℝ))^3*((3617/6000:ℝ)-r)^1 + (727566456673695744/336213480015625:ℝ)*(r-(6851/12000:ℝ))^4*((3617/6000:ℝ)-r)^0 := by unfold affine; ring
  have hp : 0≤r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma affine_cap_poly_4 {r:ℝ} (hr:r∈Icc (3617/6000:ℝ) (2/3:ℝ)) :
    (8/3:ℝ)*affine r*(1-affine r)≤r := by
  have hl : 0≤r-(3617/6000:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(2/3:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) =
    (45472903542105984/336213480015625:ℝ)*(r-(3617/6000:ℝ))^0*((2/3:ℝ)-r)^4 + (2752359841069056/2689707840125:ℝ)*(r-(3617/6000:ℝ))^1*((2/3:ℝ)-r)^3 + (300227333815296/107588313605:ℝ)*(r-(3617/6000:ℝ))^2*((2/3:ℝ)-r)^2 + (67293444556800/21517662721:ℝ)*(r-(3617/6000:ℝ))^3*((2/3:ℝ)-r)^1 + (26399424960000/21517662721:ℝ)*(r-(3617/6000:ℝ))^4*((2/3:ℝ)-r)^0 := by unfold affine; ring
  have hp : 0≤r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma affine_from_cap {r P:ℝ} (hr:r∈Icc (39/250:ℝ) (2/3:ℝ)) (hP:P≤1/2)
    (hcap:r≤(8/3:ℝ)*P*(1-P)) : affine r≤P := by
  have hr0 : 0≤r := by linarith only [hr.1]
  have h2 : r^2≤(2/3:ℝ)^2 := (sq_le_sq₀ hr0 (by norm_num)).mpr hr.2
  have h4 : r^4≤(2/3:ℝ)^4 := pow_le_pow_left₀ hr0 hr.2 4
  apply cap_envelope hP (by unfold affine; nlinarith only [h2,h4]) hcap

  by_cases h0 : r≤(617/1500:ℝ)
  · exact affine_cap_poly_0 ⟨by linarith only [hr.1],h0⟩
  by_cases h1 : r≤(539/1000:ℝ)
  · exact affine_cap_poly_1 ⟨by linarith only [h0],h1⟩
  by_cases h2 : r≤(6851/12000:ℝ)
  · exact affine_cap_poly_2 ⟨by linarith only [h1],h2⟩
  by_cases h3 : r≤(3617/6000:ℝ)
  · exact affine_cap_poly_3 ⟨by linarith only [h2],h3⟩
  exact affine_cap_poly_4 ⟨by linarith only [h3],hr.2⟩

lemma quartic_cap_poly_0 {r:ℝ} (hr:r∈Icc (79/200:ℝ) (637/1200:ℝ)) :
    (8/3:ℝ)*quartic r*(1-quartic r)≤r := by
  have hl : 0≤r-(79/200:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(637/1200:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*quartic r*(1-quartic r)-(1/10000000:ℝ) =
    (52024221825751854618624/12457785357953028025:ℝ)*(r-(79/200:ℝ))^0*((637/1200:ℝ)-r)^8 + (2022092731453728987242496/12457785357953028025:ℝ)*(r-(79/200:ℝ))^1*((637/1200:ℝ)-r)^7 + (10641317401425423011309568/12457785357953028025:ℝ)*(r-(79/200:ℝ))^2*((637/1200:ℝ)-r)^6 + (24639517032378527009875968/12457785357953028025:ℝ)*(r-(79/200:ℝ))^3*((637/1200:ℝ)-r)^5 + (6174657923095921459389696/2491557071590605605:ℝ)*(r-(79/200:ℝ))^4*((637/1200:ℝ)-r)^4 + (22098785106243529719470592/12457785357953028025:ℝ)*(r-(79/200:ℝ))^5*((637/1200:ℝ)-r)^3 + (8843151939179947854507648/12457785357953028025:ℝ)*(r-(79/200:ℝ))^6*((637/1200:ℝ)-r)^2 + (1795249145491503220347264/12457785357953028025:ℝ)*(r-(79/200:ℝ))^7*((637/1200:ℝ)-r)^1 + (145872797130502554458904/12457785357953028025:ℝ)*(r-(79/200:ℝ))^8*((637/1200:ℝ)-r)^0 := by unfold quartic; ring
  have hp : 0≤r-(8/3:ℝ)*quartic r*(1-quartic r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma quartic_cap_poly_1 {r:ℝ} (hr:r∈Icc (637/1200:ℝ) (479/800:ℝ)) :
    (8/3:ℝ)*quartic r*(1-quartic r)≤r := by
  have hl : 0≤r-(637/1200:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(479/800:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*quartic r*(1-quartic r)-(1/10000000:ℝ) =
    (37343436065408653941479424/12457785357953028025:ℝ)*(r-(637/1200:ℝ))^0*((479/800:ℝ)-r)^8 + (218329342161991435093303296/12457785357953028025:ℝ)*(r-(637/1200:ℝ))^1*((479/800:ℝ)-r)^7 + (505783344687681532854970368/12457785357953028025:ℝ)*(r-(637/1200:ℝ))^2*((479/800:ℝ)-r)^6 + (586736977997481131452704768/12457785357953028025:ℝ)*(r-(637/1200:ℝ))^3*((479/800:ℝ)-r)^5 + (76177094565115399735178496/2491557071590605605:ℝ)*(r-(637/1200:ℝ))^4*((479/800:ℝ)-r)^4 + (222056334656784469020436992/12457785357953028025:ℝ)*(r-(637/1200:ℝ))^5*((479/800:ℝ)-r)^3 + (200800305393913204441746048/12457785357953028025:ℝ)*(r-(637/1200:ℝ))^6*((479/800:ℝ)-r)^2 + (130431517445084725503713664/12457785357953028025:ℝ)*(r-(637/1200:ℝ))^7*((479/800:ℝ)-r)^1 + (32741625248235314790977304/12457785357953028025:ℝ)*(r-(637/1200:ℝ))^8*((479/800:ℝ)-r)^0 := by unfold quartic; ring
  have hp : 0≤r-(8/3:ℝ)*quartic r*(1-quartic r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma quartic_cap_poly_2 {r:ℝ} (hr:r∈Icc (479/800:ℝ) (2/3:ℝ)) :
    (8/3:ℝ)*quartic r*(1-quartic r)≤r := by
  have hl : 0≤r-(479/800:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(2/3:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*quartic r*(1-quartic r)-(1/10000000:ℝ) =
    (32741625248235314790977304/12457785357953028025:ℝ)*(r-(479/800:ℝ))^0*((2/3:ℝ)-r)^8 + (15737379461067212446076928/498311414318121121:ℝ)*(r-(479/800:ℝ))^1*((2/3:ℝ)-r)^7 + (81672843558603292159168512/498311414318121121:ℝ)*(r-(479/800:ℝ))^2*((2/3:ℝ)-r)^6 + (235981919035699122733056000/498311414318121121:ℝ)*(r-(479/800:ℝ))^3*((2/3:ℝ)-r)^5 + (414325433731694159993241600/498311414318121121:ℝ)*(r-(479/800:ℝ))^4*((2/3:ℝ)-r)^4 + (453499398278084265246720000/498311414318121121:ℝ)*(r-(479/800:ℝ))^5*((2/3:ℝ)-r)^3 + (303087682730152112947200000/498311414318121121:ℝ)*(r-(479/800:ℝ))^6*((2/3:ℝ)-r)^2 + (113422069316840325120000000/498311414318121121:ℝ)*(r-(479/800:ℝ))^7*((2/3:ℝ)-r)^1 + (18245141539690905600000000/498311414318121121:ℝ)*(r-(479/800:ℝ))^8*((2/3:ℝ)-r)^0 := by unfold quartic; ring
  have hp : 0≤r-(8/3:ℝ)*quartic r*(1-quartic r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma quartic_from_cap {r P:ℝ} (hr:r∈Icc (79/200:ℝ) (2/3:ℝ)) (hP:P≤1/2)
    (hcap:r≤(8/3:ℝ)*P*(1-P)) : quartic r≤P := by
  have hr0 : 0≤r := by linarith only [hr.1]
  have h2 : r^2≤(2/3:ℝ)^2 := (sq_le_sq₀ hr0 (by norm_num)).mpr hr.2
  have h4 : r^4≤(2/3:ℝ)^4 := pow_le_pow_left₀ hr0 hr.2 4
  apply cap_envelope hP (by unfold quartic; nlinarith only [h2,h4]) hcap

  by_cases h0 : r≤(637/1200:ℝ)
  · exact quartic_cap_poly_0 ⟨by linarith only [hr.1],h0⟩
  by_cases h1 : r≤(479/800:ℝ)
  · exact quartic_cap_poly_1 ⟨by linarith only [h0],h1⟩
  exact quartic_cap_poly_2 ⟨by linarith only [h1],hr.2⟩

lemma large_cap_poly_0 {r:ℝ} (hr:r∈Icc (21/40:ℝ) (2/3:ℝ)) :
    (8/3:ℝ)*large r*(1-large r)≤r := by
  have hl : 0≤r-(21/40:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(2/3:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*large r*(1-large r)-(1/10000000:ℝ) =
    (22643631/20880250:ℝ)*(r-(21/40:ℝ))^0*((2/3:ℝ)-r)^4 + (631811232/10440125:ℝ)*(r-(21/40:ℝ))^1*((2/3:ℝ)-r)^3 + (2057374848/10440125:ℝ)*(r-(21/40:ℝ))^2*((2/3:ℝ)-r)^2 + (2438965632/10440125:ℝ)*(r-(21/40:ℝ))^3*((2/3:ℝ)-r)^1 + (3041528224/31320375:ℝ)*(r-(21/40:ℝ))^4*((2/3:ℝ)-r)^0 := by unfold large; ring
  have hp : 0≤r-(8/3:ℝ)*large r*(1-large r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma large_from_cap {r P:ℝ} (hr:r∈Icc (21/40:ℝ) (2/3:ℝ)) (hP:P≤1/2)
    (hcap:r≤(8/3:ℝ)*P*(1-P)) : large r≤P := by
  have hr0 : 0≤r := by linarith only [hr.1]
  have h2 : r^2≤(2/3:ℝ)^2 := (sq_le_sq₀ hr0 (by norm_num)).mpr hr.2
  have h4 : r^4≤(2/3:ℝ)^4 := pow_le_pow_left₀ hr0 hr.2 4
  apply cap_envelope hP (by unfold large; nlinarith only [h2,h4]) hcap

  exact large_cap_poly_0 ⟨by linarith only [hr.1],hr.2⟩

end GaussianPropeller.FourCertificates

end OAI
